package gapt.formats.tptp

import gapt.expr.Abs
import gapt.expr.Apps
import gapt.expr.formula.All
import gapt.expr.formula.Ex
import gapt.expr.formula.Neg
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.fol.FOLFunctionConst
import gapt.expr.formula.hol.freeFOLVariables
import gapt.expr.given
import gapt.expr.substitute
import gapt.formats.tptp.*
import gapt.logic.hol.SkolemFunctions
import gapt.proofs.Ant
import gapt.proofs.RichFormulaSequent
import gapt.proofs.Sequent
import gapt.proofs.context.facet.ProofNames
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.context.update.ProofDeclaration
import gapt.proofs.expansion.ExpansionProofToLK
import gapt.proofs.expansion.deskolemizeET
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.ExistsSkLeftRule
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.rules.macros.ForallLeftBlock
import gapt.proofs.lk.rules.macros.ForallRightBlock
import gapt.proofs.lk.transformations.LKToExpansionProof
import gapt.proofs.lk.util.instantiateProof
import gapt.provers.ResolutionProver
import gapt.provers.escargot.Escargot
import gapt.utils.Maybe

import scala.util.boundary

import boundary.break

type LabelledSequent = Sequent[(String, FOLFormula)]

/**
* Attempts to replay the inferences in the given RootedTstpDerivation into an LKProof.
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
* succeedent the designated formula of the given RootedTstpDerivation and in the
* antecedent it contains the axioms of the RootedTstpDerivation and possibly its
* negated conjectures. The same axiom or negated conjecture occurs once for every
* use of the axiom or negated conjecture in the derivation in the unwrapped proof tree
*
* No guarantees are made about the order of the formulas in the sequent.
*/
def rootedTstpDerivationToLKProof(
    derivation: RootedTstpDerivation,
    prover: ResolutionProver = Escargot
): Either[
  IncorrectInference | IncorrectSkolemization | DeskolemizationFailed | ProofReconstructionError,
  LKProof
] = boundary {
  val steps = derivation.topologicallySortedUsedDerivationSteps.toSeq.reverse
  given context: MutableContext = MutableContext.guess(steps.map(_.formula))

  def replayProof(inferenceName: String, sequentToProve: Sequent[FOLFormula]): LKProof = {
    try {
      prover.getLKProof(sequentToProve).getOrElse {
        break(Left(IncorrectInference(inferenceName)))
      }
    } catch {
      case e: IllegalArgumentException =>
        // this means there was an issue with adding to context in prover
        // which likely means a skolem constant got bound with different
        // types which is incorrect
        break(Left(ProofReconstructionError(inferenceName)))
    }
  }

  def addParentProofLinks(proof: LKProof, parents: Seq[String]): LKProof = {
    parents.foldLeft(proof) { (proof, parent) =>
      val parentProofLink = context.get[ProofNames].link(FOLConst(parent)).get
      CutRule(parentProofLink, proof)
    }
  }

  def proofDeclaration(name: String, proof: LKProof, parents: Seq[String]): ProofDeclaration = {
    val freeVars = freeFOLVariables(proof.conclusion.toImplication).toSeq
    val const = FOLFunctionConst(name, freeVars.size)
    val lhs = Apps(const, freeVars)
    ProofDeclaration(lhs, addParentProofLinks(proof, parents))
  }

  steps.foreach { s =>
    s match {
      case s: TstpAxiomStep => {
        context += proofDeclaration(s.name, LogicalAxiom(s.formula), Seq.empty)
      }
      case s: TstpConjectureStep => {
        context += proofDeclaration(s.name, LogicalAxiom(Neg(s.formula)), Seq.empty)
      }
      case s: TstpNegatedConjectureStep => {
        val parentFormula = derivation.get(s.parent).get.formula
        val negatedConjectureToFormulaProof =
          replayProof(s.name, Neg(parentFormula) +: Sequent() :+ s.formula)
        val _ = replayProof(s.name, s.formula +: Sequent() :+ Neg(parentFormula))

        context += proofDeclaration(s.name, negatedConjectureToFormulaProof, s.parents)
      }
      case s: TstpSkolemizationStep => {
        val TstpSkolemizationStep(
          name,
          claimedSkolemizedFormula,
          parent,
          _,
          newSkolemSymbol,
          claimedContextVariables,
          claimedBoundVariable,
          _
        ) = s
        def reportIncorrect(): Nothing = break(Left(IncorrectSkolemization(s.name)))

        val parentFormula = derivation.get(parent).get.formula
        val All.Block(actualContextVariables, mainSkolemizationFormula) = parentFormula

        val (actualBoundVariable, innerSkolemizationFormula) = mainSkolemizationFormula match {
          case Ex(actualBoundVariable, inner) => (actualBoundVariable, inner)
          case f =>
            s"skolemization step $name claims to skolemize bound variable $claimedBoundVariable, but there is no existential quantifier following after the outermost universal quantifiers. got $f inside universal quantifier block of parent formula $parentFormula"
            reportIncorrect()
        }

        if claimedBoundVariable != actualBoundVariable then {
          s"skolemization step $name claims to skolemize bound variable $claimedBoundVariable, but the actual outer most existential variable in $parentFormula is $actualBoundVariable"
          reportIncorrect()
        }

        if claimedContextVariables.toSet != actualContextVariables.toSet then {
          s"skolemization step $name claims to have context variables $claimedContextVariables, but the actual context variables for $claimedBoundVariable are $actualContextVariables"
          reportIncorrect()
        }

        val claimedSkolemTerm = newSkolemSymbol(claimedContextVariables*)
        val innerSubstituted = innerSkolemizationFormula.substitute(claimedBoundVariable -> claimedSkolemTerm)
        val expectedSkolemizedFormula = All.Block(actualContextVariables, innerSubstituted)

        val axiom = LogicalAxiom(innerSubstituted)
        val existsSkLeft = ExistsSkLeftRule(axiom, Ant(0), mainSkolemizationFormula, claimedSkolemTerm)
        val forallLeft = ForallLeftBlock(existsSkLeft, parentFormula, actualContextVariables)
        val forallRight = ForallRightBlock(forallLeft, expectedSkolemizedFormula, actualContextVariables)
        if expectedSkolemizedFormula != claimedSkolemizedFormula then {
          s"skolemization step $name claims to skolemize formula $parentFormula by replacing $claimedBoundVariable with $claimedSkolemTerm which should result in $expectedSkolemizedFormula but the given formula is $claimedSkolemizedFormula"
          reportIncorrect()
        }
        try {
          context += { ctx =>
            import gapt.proofs.context.facet.skolemFunsFacet
            val skolemDefinition = Abs.Block(actualContextVariables, Ex(actualBoundVariable, innerSkolemizationFormula))
            ctx.state.update[SkolemFunctions](sf => sf + (newSkolemSymbol, skolemDefinition))
          }
        } catch {
          case e: IllegalArgumentException => break(Left(DeskolemizationFailed(Some(e))))
        }
        try {
          context += proofDeclaration(name, forallRight, Seq(parent))
        } catch {
          case e: IllegalArgumentException => break(Left(ProofReconstructionError(s.name)))
        }
      }

      case s: TstpPlainInferenceStep => {
        val parentFormulas = s.parents.map(p => derivation.get(p).get.formula)
        val sequentToProve = Sequent(parentFormulas, Vector(s.formula))
        val proof = replayProof(s.name, sequentToProve)
        context += proofDeclaration(s.name, proof, s.parents)
      }
    }
  }

  val proof = instantiateProof(FOLConst(derivation.root.name))(using context)
  val deskolemizedExpansionProof = {
    try deskolemizeET(LKToExpansionProof(proof))
    catch {
      case e: IllegalArgumentException =>
        break(Left(DeskolemizationFailed(Some(e))))
    }
  }
  val deskolemizedLKProof = ExpansionProofToLK(deskolemizedExpansionProof).getOrElse {
    break(Left(DeskolemizationFailed(None)))
  }
  Right(deskolemizedLKProof)
}
