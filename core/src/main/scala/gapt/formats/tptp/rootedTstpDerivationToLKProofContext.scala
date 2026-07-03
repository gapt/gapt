package gapt.formats.tptp

import gapt.expr.Abs
import gapt.expr.Expr
import gapt.expr.formula.All
import gapt.expr.formula.Ex
import gapt.expr.formula.Neg
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.fol.FOLFunctionConst
import gapt.expr.given
import gapt.expr.substitute
import gapt.expr.ty.Ti
import gapt.expr.util.constants
import gapt.formats.tptp.*
import gapt.proofs.Ant
import gapt.proofs.Sequent
import gapt.proofs.context.Context
import gapt.proofs.context.facet.ProofNames
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.context.update.ProofDeclaration
import gapt.proofs.context.update.Sort
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.ExistsSkLeftRule
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.rules.macros.ForallLeftBlock
import gapt.proofs.lk.rules.macros.ForallRightBlock
import gapt.provers.ResolutionProver
import gapt.provers.escargot.Escargot
import gapt.utils.Maybe
import gapt.utils.getOrBreak
import gapt.proofs.context.immutable.ImmutableContext
import gapt.expr.Const
import gapt.logic.hol.SkolemFunctions
import gapt.proofs.lk.rules.ImpRightRule
import gapt.proofs.Suc
import gapt.proofs.lk.rules.AndRightRule
import gapt.proofs.lk.rules.WeakeningLeftRule

import scala.util.boundary
import boundary.break
import scala.util.boundary.Label
import gapt.proofs.lk.rules.ProofLink

/**
* Attempts to replay the inferences in the given RootedTstpDerivation into an Context and a ProofLink
* such that instantiating the ProofLink in the context gives the full LKProof.
*/
def rootedTstpDerivationToLKProofContext(
    derivation: RootedTstpDerivation,
    prover: ResolutionProver = Escargot
): Either[IncorrectInference | IncorrectSkolemization, (ProofLink, Context)] = boundary { outer ?=>
  val (ctx, verifiedSkolemizationsByStepName) = constructTstpDerivationContext(derivation).getOrBreak
  given context: MutableContext = ctx.newMutable

  def replayProof(inferenceName: String, sequentToProve: Sequent[FOLFormula]): LKProof = {
    prover.getLKProof(sequentToProve).getOrElse {
      break(Left(IncorrectInference(inferenceName)))
    }
  }

  def proofDeclaration(name: String, proof: LKProof, parents: Seq[String]): ProofDeclaration = {
    val cutProof = parents.foldLeft(proof) { (proof, parent) =>
      val parentProofLink = context.get[ProofNames].link(FOLConst(parent)).get
      CutRule(parentProofLink, proof)
    }
    ProofDeclaration(FOLConst(name), cutProof)
  }

  derivation.stepsTopologicallyOrderedFromLeafsToRoot.foreach { s =>
    s match {
      case _: TstpConjectureStep =>
      case s: TstpAxiomStep => {
        context += proofDeclaration(s.name, LogicalAxiom(s.formula), Seq.empty)
      }

      case s: TstpNegatedConjectureStep => {
        val parentFormula = derivation.get(s.parent).get.formula

        // in the following we construct a proof of Neg(conjecture) :- s.formula
        // which is the only thing that is necessary for the refutation.
        // However, TSTP requires to check that the negated conjecture formula
        // is equivalent to the negation of the conjecture.
        // To represent this in the LKProof we construct a proof of
        // :- Neg(conjecture) <-> s.formula and cut it with a proof of
        // Neg(conjecture) <-> s.formula, Neg(conjecture) :- s.formula
        // which results from the proof of Neg(conjecture) :- s.formula by
        // weakening
        val negatedConjectureToFormulaProof =
          replayProof(s.name, Neg(parentFormula) +: Sequent() :+ s.formula)
        val formulaToNegatedConjectureProof =
          replayProof(s.name, s.formula +: Sequent() :+ Neg(parentFormula))
        val iffProof = AndRightRule(
          ImpRightRule(negatedConjectureToFormulaProof, Ant(0), Suc(0)),
          Suc(0),
          ImpRightRule(formulaToNegatedConjectureProof, Ant(0), Suc(0)),
          Suc(0)
        )
        val weakenedProof = WeakeningLeftRule(negatedConjectureToFormulaProof, iffProof.conclusion.succedent.head)
        val cutProof = CutRule(iffProof, weakenedProof)

        context += proofDeclaration(s.name, cutProof, Seq.empty)
      }

      case s: TstpSkolemizationStep => {
        val skolemizationStep = verifiedSkolemizationsByStepName(s.name)
        context += proofDeclaration(s.name, skolemizationStep.proof, Seq(s.parent))
      }

      case s: TstpPlainInferenceStep => {
        val parentFormulas = s.parents.map(p => derivation.get(p).get.formula)
        val sequentToProve = Sequent(parentFormulas, Vector(s.formula))
        val proof = replayProof(s.name, sequentToProve)
        context += proofDeclaration(s.name, proof, s.parents)
      }
    }
  }

  val proofLink = ProofLink(derivation.root.name)(using context)
  Right((proofLink, context.toImmutable))
}

private def constructTstpDerivationContext(
    derivation: RootedTstpDerivation
): Either[IncorrectSkolemization, (ImmutableContext, Map[String, VerifiedSkolemization])] = boundary {
  val verifiedSkolemizationsByStepName = derivation.stepsIterator.collect {
    case step: TstpSkolemizationStep => {
      val parentFormula = derivation.get(step.parent).get.formula
      val locallyCorrectSkolemization =
        VerifiedSkolemization.fromTstpSkolemizationStepAndParentFormula(step, parentFormula).getOrBreak

      (step.name, locallyCorrectSkolemization)
    }
  }.toMap

  val verifiedSkolemDefinitions = ensureCompatibleSkolemDefinitions(verifiedSkolemizationsByStepName).getOrBreak

  val _ = ensureSkolemSymbolsDistinctFromInput(derivation, verifiedSkolemDefinitions).getOrBreak

  val context: MutableContext = MutableContext.default()
  context += Sort(Ti)

  def addConstantToContextIfNotPresent(c: Const): Unit = {
    if context.constant(c.name).isEmpty
    then context += c
  }

  derivation.stepsIterator.foreach { s =>
    constants.all(s.formula).foreach { c =>
      addConstantToContextIfNotPresent(c)
    }
  }
  verifiedSkolemDefinitions.foreach {
    case (_, (symbol, definition, _)) => {
      import gapt.proofs.context.facet.skolemFunsFacet
      addConstantToContextIfNotPresent(symbol)
      context += { ctx => ctx.state.update[SkolemFunctions](_ + (symbol, definition)) }
    }
  }

  Right((context.toImmutable, verifiedSkolemizationsByStepName))
}

type SkolemDefinition = Expr
type SkolemSymbol = FOLFunctionConst
type SkolemSymbolName = String
private case class VerifiedSkolemization private (
    skolemSymbol: SkolemSymbol,
    skolemDefinition: SkolemDefinition,
    proof: LKProof
)

object VerifiedSkolemization {
  def fromTstpSkolemizationStepAndParentFormula(
      skolemizationStep: TstpSkolemizationStep,
      parentFormula: FOLFormula
  ): Either[IncorrectSkolemization, VerifiedSkolemization] = boundary {
    val TstpSkolemizationStep(
      name,
      claimedSkolemizedFormula,
      parent,
      source,
      newSkolemSymbol,
      claimedContextVariables,
      claimedBoundVariable,
      _
    ) = skolemizationStep

    val All.Block(actualContextVariables, mainSkolemizationFormula) = parentFormula

    if actualContextVariables.distinct != actualContextVariables then {
      reportIncorrectSkolemization(NonRectifiedFormula(name, parentFormula))
    }

    val (actualBoundVariable, innerSkolemizationFormula) = mainSkolemizationFormula match {
      case Ex(actualBoundVariable, inner) => (actualBoundVariable, inner)
      case f =>
        reportIncorrectSkolemization(NoExistentialQuantifierAfterRootUniversalBlock(name, claimedBoundVariable, f, parentFormula))
    }

    if claimedBoundVariable != actualBoundVariable then {
      reportIncorrectSkolemization(BoundVariableMismatch(name, claimedBoundVariable, actualBoundVariable, parentFormula))
    }

    if claimedContextVariables != actualContextVariables then {
      reportIncorrectSkolemization(ContextVariableMismatch(name, claimedContextVariables, actualContextVariables, claimedBoundVariable, parentFormula))
    }

    val claimedSkolemTerm = newSkolemSymbol(claimedContextVariables*)
    val innerSubstituted = innerSkolemizationFormula.substitute(claimedBoundVariable -> claimedSkolemTerm)
    val expectedSkolemizedFormula = All.Block(actualContextVariables, innerSubstituted)

    if expectedSkolemizedFormula != claimedSkolemizedFormula then {
      reportIncorrectSkolemization(FormulaMismatch(name, claimedSkolemizedFormula, claimedBoundVariable, claimedSkolemTerm, expectedSkolemizedFormula, parentFormula))
    }
    val skolemDefinition = Abs.Block(actualContextVariables, mainSkolemizationFormula)

    val axiom = LogicalAxiom(innerSubstituted)
    val existsSkLeft = ExistsSkLeftRule(axiom, Ant(0), mainSkolemizationFormula, claimedSkolemTerm)
    val forallLeft = ForallLeftBlock(existsSkLeft, parentFormula, actualContextVariables)
    val skolemizationProof = ForallRightBlock(forallLeft, expectedSkolemizedFormula, actualContextVariables)

    Right(new VerifiedSkolemization(newSkolemSymbol, skolemDefinition, skolemizationProof))
  }
}

private def ensureCompatibleSkolemDefinitions(
    skolemizationsByStepName: Map[String, VerifiedSkolemization]
): Either[IncorrectSkolemization, Map[String, (FOLFunctionConst, Expr, Set[String])]] = boundary {
  val skolemizationsBySkolemSymbolName =
    skolemizationsByStepName.groupBy((_, skolemization) => skolemization.skolemSymbol.name)

  val verifiedSkolemDefinitions = skolemizationsBySkolemSymbolName.map {
    case s @ (skolemSymbolName, definitionsByStepName) => {
      val incompatibilities = incompatibleSkolemDefinitions(definitionsByStepName)
      if incompatibilities.nonEmpty then {
        reportIncorrectSkolemization(MultipleIncompatibleSkolemDefinitionsOfSameSymbol(skolemSymbolName, incompatibilities))
      }

      val uniqueDefinitions = definitionsByStepName.map((_, skolemization) => (skolemization.skolemSymbol, skolemization.skolemDefinition)).toSet
      assert(uniqueDefinitions.size == 1, s"skolem symbol ${skolemSymbolName} has multiple incompatible definitions: $uniqueDefinitions")
      val (skolemConst, definition) = uniqueDefinitions.head
      val stepNames = definitionsByStepName.keySet
      (skolemSymbolName, (skolemConst, definition, stepNames))
    }
  }.toMap

  Right(verifiedSkolemDefinitions)
}

private def ensureSkolemSymbolsDistinctFromInput(
    derivation: RootedTstpDerivation,
    verifiedSkolemDefinitions: Map[String, (FOLFunctionConst, Expr, Set[String])]
): Either[IncorrectSkolemization, Unit] = boundary {
  val inputSymbols = derivation.stepsIterator.collect {
    case s: TstpAxiomStep      => s.name -> constants.nonLogical(s.formula)
    case s: TstpConjectureStep => s.name -> constants.nonLogical(s.formula)
  }.toMap

  inputSymbols.foreach { (stepName, symbols) =>
    symbols.foreach { symbol =>
      verifiedSkolemDefinitions.get(symbol.name).foreach { (_, _, skolemizationStepNames) =>
        reportIncorrectSkolemization(SkolemSymbolIsAConstantExistingInTheInput(
          stepName,
          skolemizationStepNames.head,
          symbol
        ))
      }
    }
  }

  Right(())
}

private def incompatibleSkolemDefinitions(
    skolemizationsByStepName: Map[String, VerifiedSkolemization]
): Map[String, VerifiedSkolemization] = {
  skolemizationsByStepName.toSeq.combinations(2).foldLeft(Map.empty) {
    case (acc, Seq((leftStep, leftSkolemization), (rightStep, rightSkolemization))) => {
      val leftSymbol = leftSkolemization.skolemSymbol
      val leftDefinition = leftSkolemization.skolemDefinition
      val rightSymbol = rightSkolemization.skolemSymbol
      val rightDefinition = rightSkolemization.skolemDefinition
      assert(leftSymbol.name == rightSymbol.name, s"skolem symbol names do not match: ${leftSymbol.name} != ${rightSymbol.name}")
      if leftDefinition == rightDefinition then acc
      else acc ++ Set((leftStep, leftSkolemization), (rightStep, rightSkolemization))
    }
    case _ => throw new AssertionError("cannot happen as we only select 2 combinations")
  }
}

private def reportIncorrectSkolemization[T](
    reason: IncorrectSkolemizationReason
)(using Label[Left[IncorrectSkolemization, Nothing]]): Nothing =
  break(Left(IncorrectSkolemization(reason)))
