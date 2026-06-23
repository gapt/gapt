package gapt.formats.tptp

import gapt.expr.formula.Neg
import gapt.expr.formula.fol.FOLFormula
import gapt.formats.tptp.*
import gapt.proofs.Ant
import gapt.proofs.Sequent
import gapt.proofs.Suc
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.CutRule
import gapt.provers.ResolutionProver
import gapt.provers.escargot.Escargot

import scala.util.boundary
import boundary.break
import gapt.proofs.lk.rules.ExistsSkLeftRule
import gapt.expr.formula.Ex
import gapt.expr.{substitute, given}
import gapt.expr.formula.All
import gapt.proofs.lk.rules.macros.ForallLeftBlock
import gapt.proofs.lk.rules.macros.ForallRightBlock
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.expansion.deskolemizeET
import gapt.proofs.lk.transformations.LKToExpansionProof
import gapt.proofs.context.mutable.MutableContext
import gapt.utils.Maybe
import gapt.proofs.expansion.ExpansionProofToLK

type LabelledSequent = Sequent[(String, FOLFormula)]

/**
* Attempts to replay the inferences in the given RootedTptpDerivation into an LKProof.
*
* Builds a labelled sequent for every inference step where the antecedent is composed
* of the parent formulas of the step and the succeedent is the introduced formula by the
* step. The labels are determined by the step names from the TPTP derivation
*
* Then runs the given prover to find LKProofs for these sequents. If any fails,
* then the replay fails with an error.
*
* If all replays succeed, glues the resulting proofs together with cuts based on the
* labels to form the resulting LKProof. The end sequent of this LKProof has in the
* succeedent the designated formula of the given RootedTptpDerivation and in the
* antecedent it contains the axioms of the RootedTptpDerivation and possibly its
* negated conjectures. The same axiom or negated conjecture occurs once for every
* use of the axiom or negated conjecture in the derivation in the unwrapped proof tree
*
* No guarantees are made about the order of the formulas in the sequent.
*/
def rootedTptpDerivationToLKProof(
    derivation: RootedTptpDerivation,
    prover: ResolutionProver = Escargot
): Either[IncorrectInference | DeskolemizationFailed, LKProof] = boundary {
  given Maybe[MutableContext] = (MutableContext.guess(derivation.usedDerivationSteps.map(_.formula))).newMutable
  val stepProofsByName: Map[String, (LabelledSequent, LKProof)] = derivation.usedDerivationSteps.map { s =>
    val sequentToProve: LabelledSequent = s match {
      case TptpAxiomStep(name, formula, _) =>
        Sequent(Vector((name, formula)), Vector((name, formula)))
      case TptpConjectureStep(name, formula, _) =>
        Sequent(Vector((name, Neg(formula))), Vector((name, Neg(formula))))
      case TptpPlainInferenceStep(name, formula, parents, _) =>
        Sequent(parents.map(p => (p, derivation.get(p).get.formula)), Vector((name, formula)))
      case TptpNegatedConjectureStep(name, formula, parent, _) =>
        Sequent(Vector((parent, Neg(derivation.get(parent).get.formula))), Vector((name, formula)))
      case TptpSkolemizationStep(name, formula, parent, _, _, _, _) =>
        Sequent(Vector((parent, derivation.get(parent).get.formula)), Vector((name, formula)))
    }

    val proofOption = s match {
      case TptpAxiomStep(name, formula, annotationsOption)      => Some(LogicalAxiom(formula))
      case TptpConjectureStep(name, formula, annotationsOption) => Some(LogicalAxiom(Neg(formula)))
      case s @ TptpSkolemizationStep(name, claimedSkolemizedFormula, parent, newSkolemSymbol, claimedContextVariables, claimedBoundVariable, _) => {
        def reportIncorrect(message: String): Nothing = break(Left(IncorrectInference(message, s.name)))

        val parentFormula = derivation.get(parent).get.formula
        if parentFormula.contains(newSkolemSymbol) then {
          reportIncorrect(s"skolemization step $name has skolemSymbol $newSkolemSymbol which is already used in $parentFormula")
        }
        val All.Block(actualContextVariables, mainSkolemizationFormula) = parentFormula

        val (actualBoundVariable, innerSkolemizationFormula) = mainSkolemizationFormula match {
          case Ex(actualBoundVariable, inner) => (actualBoundVariable, inner)
          case f =>
            reportIncorrect(s"skolemization step $name claims to skolemize bound variable $claimedBoundVariable, but there is no existential quantifier following after the outermost universal quantifiers. got $f inside universal quantifier block of parent formula $parentFormula")
        }

        if claimedBoundVariable != actualBoundVariable then {
          reportIncorrect(s"skolemization step $name claims to skolemize bound variable $claimedBoundVariable, but the actual outer most existential variable in $parentFormula is $actualBoundVariable")
        }

        if claimedContextVariables.toSet != actualContextVariables.toSet then {
          reportIncorrect(s"skolemization step $name claims to have context variables $claimedContextVariables, but the actual context variables for $claimedBoundVariable are $actualContextVariables")
        }

        val claimedSkolemTerm = newSkolemSymbol(claimedContextVariables*)
        val innerSubstituted = innerSkolemizationFormula.substitute(claimedBoundVariable -> claimedSkolemTerm)
        val expectedSkolemizedFormula = All.Block(actualContextVariables, innerSubstituted)

        val axiom = LogicalAxiom(innerSubstituted)
        val existsSkLeft = ExistsSkLeftRule(axiom, Ant(0), mainSkolemizationFormula, claimedSkolemTerm)
        val forallLeft = ForallLeftBlock(existsSkLeft, parentFormula, actualContextVariables)
        val forallRight = ForallRightBlock(forallLeft, expectedSkolemizedFormula, actualContextVariables)
        if expectedSkolemizedFormula != claimedSkolemizedFormula then {
          reportIncorrect(s"skolemization step $name claims to skolemize formula $parentFormula by replacing $claimedBoundVariable with $claimedSkolemTerm which should result in $expectedSkolemizedFormula but the given formula is $claimedSkolemizedFormula")
        }
        Some(forallRight)
      }
      case _ => prover.getLKProof(sequentToProve.map(_._2))
    }

    val proof = proofOption match {
      case None    => break(Left(IncorrectInference(s"inference with label ${s.name} is incorrect", s.name)))
      case Some(p) => p
    }

    val sequentSorted = sortSequentLike(sequentToProve, proof.conclusion.asInstanceOf[Sequent[FOLFormula]])

    (s.name, (sequentSorted, proof))
  }.toMap

  def cutProofsStartingFrom(name: String): (LabelledSequent, LKProof) = derivation.get(name).get match {
    case TptpAxiomStep(_, _, _) | TptpConjectureStep(_, _, _) => stepProofsByName(name)

    case _ => {
      val p @ (sequent, proof) = stepProofsByName(name)
      sequent.antecedent.foldLeft(p) {
        case ((s, p), (label, formula)) => {
          val (parentSequent, parentProof) = cutProofsStartingFrom(label)
          assert(parentProof.conclusion.succedent.size == 1, s"parentProof.conclusion.succedent.size = ${parentProof.conclusion.succedent.size}, label = $label")
          assert(
            parentProof.conclusion.succedent.head == formula,
            s"parentProof.conclusion.succedent.head = ${parentProof.conclusion.succedent.head}, formula = $formula, label = $label"
          )
          val index = Ant(s.antecedent.indexWhere((l, _) => l == label))
          assert(index.k >= 0, s"index = $index, label = $label")
          assert(p.conclusion(index) == formula, s"p.conclusion($index) = ${p.conclusion(index)}, formula = $formula")
          val updatedProof: LKProof = CutRule(parentProof, Suc(0), p, index)
          val cutSequent: LabelledSequent = s.delete(index) ++ parentSequent.delete(Suc(0))
          val sortedCutSequent = sortSequentLike(cutSequent, updatedProof.conclusion.asInstanceOf[Sequent[FOLFormula]])
          (sortedCutSequent, updatedProof)
        }
      }
    }
  }

  val (_, proof) = cutProofsStartingFrom(derivation.root.name)
  val deskolemizedExpansionProof = {
    try deskolemizeET(LKToExpansionProof(proof))
    catch
      case e: IllegalArgumentException =>
        break(Left(DeskolemizationFailed(proof, Some(e))))
  }
  val deskolemizedLKProof = ExpansionProofToLK(deskolemizedExpansionProof).getOrElse {
    break(Left(DeskolemizationFailed(proof, None)))
  }
  Right(deskolemizedLKProof)
}

// Escargot.getLKProof does not guarantee that the conclusion of the output proof
// is the same sequent as the input sequent. Therefore we sort our given labelled sequent
// based on the order of formulas in the given target sequent given from the Escargot
// proof. This is necessary so we can glue together the individual step proofs
// on the right formulas which allows for a more faithful representation of the
// TptpDerivation as an LKProof
private def sortSequentLike(source: LabelledSequent, target: Sequent[FOLFormula]): LabelledSequent = {
  assert(
    target.multiSetEquals(source.map(_._2)),
    s"sequents are not equal up to multiset equality source = $source, target = ${target}"
  )
  val (antecedentSorted, remainder) = target.antecedent.foldLeft((Vector.empty[(String, FOLFormula)], source.antecedent)) {
    case ((newSequent, oldSequent), formula) => {
      val index = oldSequent.indexWhere((_, f) => f == formula)
      assert(index >= 0, s"index not found, formula = $formula, oldSequent = $oldSequent, source = $source, target = $target")
      val element = oldSequent(index)
      (newSequent :+ element, oldSequent.take(index) ++ oldSequent.drop(index + 1))
    }
  }
  assert(remainder.isEmpty, s"remainder = $remainder")
  val result = Sequent(antecedentSorted, source.succedent)
  assert(result.map(_._2) == target, s"result = $result, proof.conclusion = ${target}")
  result
}
