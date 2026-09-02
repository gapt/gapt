package gapt.formats.tptp.check

import gapt.expr.Abs
import gapt.expr.App
import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.Var
import gapt.expr.formula.*
import gapt.expr.formula.Formula
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.fol.FOLFunctionConst
import gapt.expr.formula.fol.FOLTerm
import gapt.expr.formula.fol.FOLVar
import gapt.expr.formula.hol.HOLPosition
import gapt.expr.given
import gapt.expr.substitute
import gapt.expr.ty.Ti
import gapt.expr.util.constants
import gapt.expr.util.freeVariables
import gapt.formats.InputFile
import gapt.formats.tptp.*
import gapt.formats.tptp.check.FindSkolemizableInstance.QuantifierType
import gapt.logic.Polarity
import gapt.logic.Polarity.Negative
import gapt.logic.Polarity.Positive
import gapt.logic.hol.SkolemFunctions
import gapt.proofs.Ant
import gapt.proofs.Sequent
import gapt.proofs.Suc
import gapt.proofs.context.Context
import gapt.proofs.context.State
import gapt.proofs.context.facet.ProofNames
import gapt.proofs.context.immutable.ImmutableContext
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.context.update.ProofDefinitionDeclaration
import gapt.proofs.context.update.ProofNameDeclaration
import gapt.proofs.context.update.Sort
import gapt.proofs.context.update.Update
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.AndLeftRule
import gapt.proofs.lk.rules.AndRightRule
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.ExistsLeftRule
import gapt.proofs.lk.rules.ExistsRightRule
import gapt.proofs.lk.rules.ExistsSkLeftRule
import gapt.proofs.lk.rules.ForallLeftRule
import gapt.proofs.lk.rules.ForallRightRule
import gapt.proofs.lk.rules.ForallSkRightRule
import gapt.proofs.lk.rules.ImpLeftRule
import gapt.proofs.lk.rules.ImpRightRule
import gapt.proofs.lk.rules.LogicalAxiom
import gapt.proofs.lk.rules.NegLeftRule
import gapt.proofs.lk.rules.NegRightRule
import gapt.proofs.lk.rules.OrLeftRule
import gapt.proofs.lk.rules.OrRightRule
import gapt.proofs.lk.rules.ProofLink
import gapt.proofs.lk.rules.WeakeningLeftRule
import gapt.provers.ResolutionProver
import gapt.provers.escargot.Escargot
import gapt.utils.Maybe
import gapt.utils.getOrBreak

import java.nio.file.Paths
import java.util.concurrent.atomic.AtomicInteger
import scala.concurrent.Await
import scala.concurrent.ExecutionContext
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.Future
import scala.concurrent.Promise
import scala.concurrent.duration.Duration
import scala.util.Failure
import scala.util.Success
import scala.util.boundary
import scala.util.boundary.Label
import scala.util.control.NonFatal

import boundary.break
import gapt.utils.NameGenerator

sealed trait TstpDerivationError {
  def message: String
}
sealed trait VerifiedBadReason extends TstpDerivationError
sealed trait VerifiedUnknownReason extends TstpDerivationError

enum SzsStatus {
  case VerifiedGood
  case VerifiedBad(reason: VerifiedBadReason)
  case Unknown(reason: VerifiedUnknownReason)
  case Timeout

  def status: String = this match {
    case VerifiedGood        => "VerifiedGood"
    case VerifiedBad(reason) => s"VerifiedBad : ${reason.message.replace("\n", "\\n")}"
    case Unknown(reason)     => s"Unknown : ${reason.message.replace("\n", "\\n")}"
    case Timeout             => "Timeout"
  }
  def isGood: Boolean = this == VerifiedGood
  def isBad: Boolean = this.isInstanceOf[VerifiedBad]
  def isUnknown: Boolean = this.isInstanceOf[Unknown]

  def statusLine: String = s"% SZS status $status"
}

/**
* Attempts to replay the inferences in the given StructurallyCorrectTstpDerivation into a Context containing
* LKProofs for every inference step in the StructurallyCorrectTstpDerivation
*/
def buildTstpDerivationToProofContext(
    derivation: StructurallyCorrectTstpDerivation,
    prover: ResolutionProver = Escargot
): Either[IncorrectInference | IncorrectSkolemization, Context] = boundary { outer ?=>
  val verifiedSkolemizationsByStepName = verifiedSkolemizations(derivation).getOrBreak
  val deoverloadedDerivation = deoverloadSymbols(derivation)
  val ctx = buildTstpDerivationContext(deoverloadedDerivation, verifiedSkolemizationsByStepName)
  given context: MutableContext = ctx.newMutable

  def addToContext(update: => Update) = {
    context += update
  }

  def replayProof(inferenceName: String, sequentToProve: Sequent[FOLFormula]): LKProof =
    val replayContext = context
    prover.getLKProof(sequentToProve)(using replayContext).getOrElse {
      break(Left(IncorrectInference(inferenceName)))
    }

  case class VariableCapturingProofDeclaration(lhs: Expr, proof: LKProof) extends Update {
    def link = ProofLink(lhs, proof.endSequent)

    override def apply(ctx: Context): State =
      ctx + ProofNameDeclaration(lhs, proof.endSequent, freeVariables(proof.endSequent)) + ProofDefinitionDeclaration(lhs, proof) state

    override def toString: String =
      s"VariableCapturingProofDeclaration($lhs, ${proof.endSequent})"
  }

  def proofDeclaration(name: String, proof: LKProof, parents: Seq[String]): VariableCapturingProofDeclaration = {
    val cutProof = parents.foldLeft(proof) { (proof, parent) =>
      val parentProofLink = context.get[ProofNames].link(FOLConst(parent)).get
      CutRule(parentProofLink, proof)
    }
    VariableCapturingProofDeclaration(FOLConst(name), cutProof)
  }

  def handleStep(s: ParsedTstpDerivationStep) = {
    s match {
      case _: ParsedTstpConjectureStep =>
      case s: ParsedTstpAxiomStep => {
        addToContext(proofDeclaration(s.name, LogicalAxiom(s.formula), Seq.empty))
      }

      case s: ParsedTstpNegatedConjectureStep => {
        val parentFormula = deoverloadedDerivation.get(s.parent).get.formula

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

        addToContext(proofDeclaration(s.name, cutProof, Seq.empty))
      }

      case s: ParsedTstpSkolemizationStep => {
        val skolemizationStep = verifiedSkolemizationsByStepName(s.name)
        addToContext(proofDeclaration(s.name, skolemizationStep.proof, Seq(s.parent)))
      }

      case s: ParsedTstpPlainInferenceStep => {
        val parentFormulas = s.parents.map(p => deoverloadedDerivation.get(p).get.formula)
        val sequentToProve = Sequent(parentFormulas, Vector(s.formula))
        val proof = replayProof(s.name, sequentToProve)
        addToContext(proofDeclaration(s.name, proof, s.parents))
      }
    }
  }

  deoverloadedDerivation.stepsTopologicallyOrdered.foreach(handleStep)

  Right(context.toImmutable)
}

/**
* Attempts to replay the inferences in the given StructurallyCorrectTstpDerivation, but does not create
* a context or LKProofs of the inferences for performance. Use this, if you are
* interested in whether the given derivation is correct or not, but do not care
* about the replayed proofs
*/
def checkDerivationHasNoIncorrectInferences(
    derivation: StructurallyCorrectTstpDerivation,
    prover: ResolutionProver = Escargot
): Either[IncorrectInference | IncorrectSkolemization | StepsWithOverloadedSymbols, Unit] = boundary {
  val verifiedSkolemizationsByStepName = verifiedSkolemizations(derivation).getOrBreak
  val deoverloadedDerivation = deoverloadSymbols(derivation)
  val ctx = buildTstpDerivationContext(deoverloadedDerivation, verifiedSkolemizationsByStepName)
  val context: MutableContext = ctx.newMutable

  def isValid(inferenceName: String, sequentToProve: Sequent[FOLFormula]): Boolean = {
    val replayContext = context.newMutable
    prover.isValid(sequentToProve)(using replayContext)
  }

  val futures: Seq[Future[(ParsedTstpDerivationStep, Boolean)]] = deoverloadedDerivation.stepsIterator.toSeq.flatMap {
    case s: ParsedTstpPlainInferenceStep => {
      val parentFormulas = s.parents.map(p => deoverloadedDerivation.get(p).get.formula)
      val sequentToProve = Sequent(parentFormulas, Vector(s.formula))
      Seq(Future { (s, isValid(s.name, sequentToProve)) })
    }
    case s: ParsedTstpNegatedConjectureStep => {
      val parentFormula = deoverloadedDerivation.get(s.parent).get.formula
      Seq(
        Future {
          val negatedConjectureToFormulaProof =
            isValid(s.name, Neg(parentFormula) +: Sequent() :+ s.formula)
          (s, negatedConjectureToFormulaProof)
        },
        Future {
          val formulaToNegatedConjectureProof =
            isValid(s.name, s.formula +: Sequent() :+ Neg(parentFormula))
          (s, formulaToNegatedConjectureProof)
        }
      )
    }
    case _ => Seq.empty
  }
  val incorrectStep = firstCompletedMatching(futures)((_, p) => !p)
  val result = Await.result(incorrectStep, Duration.Inf)
  result match {
    case None            => Right(())
    case Some((step, _)) => Left(IncorrectInference(step.name))
  }
}

private def firstCompletedMatching[A](futures: Iterable[Future[A]])(predicate: A => Boolean): Future[Option[A]] = {
  if futures.isEmpty then Future.successful(None)
  else {
    val result = Promise[Option[A]]()
    val remaining = new AtomicInteger(futures.size)

    def completedWithoutMatch(): Unit =
      if remaining.decrementAndGet() == 0 then
        result.trySuccess(None)

    futures.foreach { future =>
      future.onComplete {
        case Success(value) =>
          try {
            if predicate(value) then result.trySuccess(Some(value))
            else completedWithoutMatch()
          } catch {
            case NonFatal(error) => result.tryFailure(error)
          }
        case Failure(e) =>
          result.tryFailure(e)
      }
    }

    result.future
  }
}

private def verifiedSkolemizations(
    derivation: StructurallyCorrectTstpDerivation
): Either[IncorrectSkolemization, Map[String, VerifiedSkolemization]] = boundary {
  val verifiedSkolemizationsByStepName = derivation.stepsIterator.collect {
    case step: ParsedTstpSkolemizationStep => {
      val parentFormula = derivation.get(step.parent).get.formula
      val locallyCorrectSkolemization =
        VerifiedSkolemization.fromTstpSkolemizationStepAndParentFormula(step, parentFormula).getOrBreak

      (step.name, locallyCorrectSkolemization)
    }
  }.toMap

  val verifiedSkolemDefinitions = ensureCompatibleSkolemDefinitions(verifiedSkolemizationsByStepName).getOrBreak
  val _ = ensureSkolemSymbolsDistinctFromInput(derivation, verifiedSkolemDefinitions).getOrBreak
  Right(verifiedSkolemizationsByStepName)
}

private def deoverloadSymbols(derivation: StructurallyCorrectTstpDerivation): StructurallyCorrectTstpDerivation = {
  import scala.collection.mutable
  val constTable = mutable.Map.empty[String, mutable.Set[(Const, ParsedTstpDerivationStep)]]

  derivation.stepsIterator.foreach { s =>
    constants.all(s.formula).foreach { c =>
      constTable.getOrElseUpdate(c.name, mutable.Set.empty).add((c, s))
    }
  }

  val renamingTable = mutable.Map.empty[Const, String]
  val nameGenerator = new NameGenerator(Iterable.empty)
  constTable.foreach { (symbolName, constSteps) =>
    val constToSteps = constSteps.groupMap(_._1)(_._2)
    constToSteps.keys.foreach { const =>
      assert(const.name == symbolName)
      renamingTable.getOrElseUpdate(const, nameGenerator.fresh(const.name))
    }
  }

  def renamedFormula(formula: FOLFormula): FOLFormula =
    renameConsts(renamingTable)(formula).asInstanceOf[FOLFormula]

  derivation.mapSteps {
    case s: ParsedTstpAxiomStep             => s.copy(formula = renamedFormula(s.formula))
    case s: ParsedTstpConjectureStep        => s.copy(formula = renamedFormula(s.formula))
    case s: ParsedTstpNegatedConjectureStep => s.copy(formula = renamedFormula(s.formula))
    case s: ParsedTstpPlainInferenceStep    => s.copy(formula = renamedFormula(s.formula))
    case s: ParsedTstpSkolemizationStep     => s.copy(formula = renamedFormula(s.formula))
  }
}

private def buildTstpDerivationContext(derivation: StructurallyCorrectTstpDerivation, verifiedSkolemizationsByStepName: Map[String, VerifiedSkolemization]): ImmutableContext = {
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

  verifiedSkolemizationsByStepName.foreach {
    case (_, skolemization) => {
      import gapt.proofs.context.facet.skolemFunsFacet
      addConstantToContextIfNotPresent(skolemization.skolemSymbol)
      context += { ctx => ctx.state.update[SkolemFunctions](_ + (skolemization.skolemSymbol, skolemization.skolemDefinition)) }
    }
  }

  context.toImmutable
}

def renameConsts(renaming: PartialFunction[Const, String])(expr: Expr): Expr = expr match {
  case v: Var         => v
  case c: Const       => Const(renaming.applyOrElse(c, _ => c.name), c.ty, c.params)
  case App(head, arg) => App(renameConsts(renaming)(head), renameConsts(renaming)(arg))
  case Abs(v, body)   => Abs(v, renameConsts(renaming)(body))
}

type SkolemDefinition = Expr
type SkolemSymbol = FOLFunctionConst
type SkolemSymbolName = String
case class VerifiedSkolemization private (
    skolemSymbol: SkolemSymbol,
    skolemDefinition: SkolemDefinition,
    proof: LKProof
)

object VerifiedSkolemization {
  def fromTstpSkolemizationStepAndParentFormula(
      skolemizationStep: ParsedTstpSkolemizationStep,
      parentFormula: FOLFormula
  ): Either[IncorrectSkolemization, VerifiedSkolemization] =
    deepSkolemizationCheck(skolemizationStep, parentFormula)

  private def deepSkolemizationCheck(
      skolemizationStep: ParsedTstpSkolemizationStep,
      parentFormula: FOLFormula
  ) = boundary {
    val ParsedTstpSkolemizationStep(
      name,
      claimedSkolemizedFormula,
      parent,
      source,
      newSkolemSymbol,
      claimedContextVariables,
      claimedBoundVariable,
      _
    ) = skolemizationStep

    if claimedContextVariables.distinct != claimedContextVariables then {
      reportIncorrectSkolemization(NonRectifiedFormula(name, claimedSkolemizedFormula)) // TODO: find better error
    }

    val claimedSkolemTerm = newSkolemSymbol(claimedContextVariables*)
    val pol = Negative // TODO: we are assuming a negative context (i.e. if coming from an conjecture leaf, there was negated_conjecture before)
    val possibleMatches = FindSkolemizableInstance(parentFormula, claimedSkolemizedFormula, pol, claimedBoundVariable, newSkolemSymbol, claimedSkolemTerm)
    if possibleMatches.size == 0 then {
      reportIncorrectSkolemization(NoStrongQuantifierFittingSkolemization(name, parentFormula, claimedSkolemizedFormula, claimedBoundVariable, claimedSkolemTerm))
    }
    if possibleMatches.size > 1 then {
      reportIncorrectSkolemization(MultipleStrongQuantifiersFittingSkolemization(name, parentFormula, claimedSkolemizedFormula, claimedBoundVariable, claimedSkolemTerm))
    }
    val (quantifierPosition, skolemContext, parentContext) = possibleMatches(0)
    // TODO: get rid of cast
    val mainSkolemizationFormula = HOLPosition.toLambdaPosition(parentFormula)(quantifierPosition).get(parentFormula).get.asInstanceOf[FOLFormula]

    val (allContextQuantifierTypes, allContextVariables) = parentContext unzip
    val outerSkolemizationContextVariables = parentContext.collect { case (QuantifierType.Weak, x) => x.asInstanceOf[FOLVar] }

    val innerSkolemizationContextVariables = freeVariables(mainSkolemizationFormula).toSeq

    if allContextVariables.distinct != allContextVariables then {
      reportIncorrectSkolemization(NonRectifiedFormula(name, parentFormula))
    }

    if outerSkolemizationContextVariables.distinct != outerSkolemizationContextVariables then {
      reportIncorrectSkolemization(NonRectifiedFormula(name, parentFormula))
    }

    if outerSkolemizationContextVariables.contains(claimedBoundVariable) then {
      reportIncorrectSkolemization(NonRectifiedFormula(name, parentFormula))
    }

    if claimedContextVariables.toSet != outerSkolemizationContextVariables.toSet
      && claimedContextVariables.toSet != innerSkolemizationContextVariables.toSet
    then {
      reportIncorrectSkolemization(
        ContextVariableMismatch(
          name,
          claimedContextVariables,
          outerSkolemizationContextVariables,
          innerSkolemizationContextVariables,
          claimedBoundVariable,
          parentFormula
        )
      )
    }

    val skolemDefinition = Abs.Block(claimedContextVariables, mainSkolemizationFormula)

    val (parentSKVar, innerFormula) = mainSkolemizationFormula match {
      case All(v, f) => (v, f)
      case Ex(v, f)  => (v, f)
    }
    assert(parentSKVar == claimedBoundVariable, s"parentSKVar ($parentSKVar) does not match claimedBoundVariable ($claimedBoundVariable)")
    val inferredSkolemizationFormula = HOLPosition.replace(parentFormula, quantifierPosition, innerFormula.substitute(claimedBoundVariable -> claimedSkolemTerm)).asInstanceOf[FOLFormula]
    if inferredSkolemizationFormula != claimedSkolemizedFormula then {
      reportIncorrectSkolemization(FormulaMismatch(name, claimedSkolemizedFormula, claimedBoundVariable, claimedSkolemTerm, inferredSkolemizationFormula, parentFormula))
    }

    val skolemizationProof = CreateSkolemizationProof(parentFormula, inferredSkolemizationFormula, claimedBoundVariable, claimedSkolemTerm, innerFormula, quantifierPosition, pol)
    val cutWithClaimedFormula = CutRule(skolemizationProof, LogicalAxiom(claimedSkolemizedFormula)) // fixes alpha equivalence
    Right(new VerifiedSkolemization(newSkolemSymbol, skolemDefinition, cutWithClaimedFormula))
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

private def incompatibleSkolemDefinitions(
    skolemizationsByStepName: Map[String, VerifiedSkolemization]
): Map[String, VerifiedSkolemization] = {
  skolemizationsByStepName.toSeq.combinations(2).foldLeft(Map.empty) {
    case (acc, Seq((leftStep, leftSkolemization), (rightStep, rightSkolemization))) => {
      val leftSymbol = leftSkolemization.skolemSymbol
      val rightSymbol = rightSkolemization.skolemSymbol
      assert(leftSymbol.name == rightSymbol.name, s"skolem symbol names do not match: ${leftSymbol.name} != ${rightSymbol.name}")
      acc ++ Set((leftStep, leftSkolemization), (rightStep, rightSkolemization))
    }
    case _ => throw new AssertionError("cannot happen as we only select 2 combinations")
  }
}

private def ensureSkolemSymbolsDistinctFromInput(
    derivation: StructurallyCorrectTstpDerivation,
    verifiedSkolemDefinitions: Map[String, (FOLFunctionConst, Expr, Set[String])]
): Either[IncorrectSkolemization, Unit] = boundary {
  val inputSymbols = derivation.stepsIterator.collect {
    case s: ParsedTstpAxiomStep      => s.name -> constants.nonLogical(s.formula)
    case s: ParsedTstpConjectureStep => s.name -> constants.nonLogical(s.formula)
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

private def reportIncorrectSkolemization[T](
    reason: IncorrectSkolemizationReason
)(using Label[Left[IncorrectSkolemization, Nothing]]): Nothing =
  break(Left(IncorrectSkolemization(reason)))

object FindSkolemizableInstance {
  enum QuantifierType {
    case Strong
    case Weak
  }

  /**
   * Finds all positions p and variable contexts s.t. unskolemized[p] is a strongly quantified
   * formula Q skVar . F and replacing unskolemized[p] by F{skVar <- skTerm} obtains skolemized.
   */
  def apply(unskolemized: FOLFormula, skolemized: FOLFormula, polarity: Polarity, skVar: FOLVar, skConst: Const, skTerm: FOLTerm) = {
    def skQuantifier(e: Expr) = e match { case All(x, _) => skVar == x; case Ex(x, _) => skVar == x; case _ => false }
    val candidate_positions = HOLPosition.getPositions(unskolemized, skQuantifier)
    val qs = candidate_positions.filter(x => isStrongQuantifierPosition(x, unskolemized, polarity))
    // println(s"us: $unskolemized s: $skolemized candidates: $candidate_positions strong_qs: $qs")
    val correctly_skolemized = qs.filter(pos => {
      val inner_pos = HOLPosition(pos.list :+ 1)
      val lambda_pos = HOLPosition.toLambdaPosition(unskolemized)(inner_pos)
      val body = lambda_pos.get(unskolemized).get
      val reskolemized = HOLPosition.replace(unskolemized, pos, body.substitute(skVar -> skTerm))
      reskolemized == skolemized
    })
    def getContext(x: HOLPosition, f: FOLFormula) = polarityAndContextAt(x, f, polarity)._2
    correctly_skolemized.map(x => (x, getContext(x, skolemized), getContext(x, unskolemized)))
  }

  def polarityAndContextAt(pos: HOLPosition, e: Expr, polarity: Polarity, context: List[(QuantifierType, Var)] = Nil): (Polarity, List[(QuantifierType, Var)]) =
    (pos.list, e) match {
      case (Nil, _)           => (polarity, context.reverse)
      case (_, FOLAtom(_, _)) => (polarity, context.reverse)
      case (1 :: _, Neg(x))   => polarityAndContextAt(pos.tail, x, !polarity, context)
      case (1 :: _, All(v, x)) =>
        val ws = if polarity == Positive then QuantifierType.Strong else QuantifierType.Weak
        polarityAndContextAt(pos.tail, x, polarity, (ws, v) :: context)
      case (1 :: _, Ex(v, x)) =>
        val ws = if polarity == Positive then QuantifierType.Weak else QuantifierType.Strong
        polarityAndContextAt(pos.tail, x, polarity, (ws, v) :: context)
      case (1 :: _, And(x, _)) => polarityAndContextAt(pos.tail, x, polarity, context)
      case (2 :: _, And(_, x)) => polarityAndContextAt(pos.tail, x, polarity, context)
      case (1 :: _, Or(x, _))  => polarityAndContextAt(pos.tail, x, polarity, context)
      case (2 :: _, Or(_, x))  => polarityAndContextAt(pos.tail, x, polarity, context)
      case (1 :: _, Imp(x, _)) => polarityAndContextAt(pos.tail, x, !polarity, context)
      case (2 :: _, Imp(_, x)) => polarityAndContextAt(pos.tail, x, polarity, context)
      case _                   => throw new Exception(s"Could not find polarity of $pos in $e")
    }

  def isStrongQuantifierPosition(pos: HOLPosition, e: Expr, polarity: Polarity): Boolean = {
    val pol = polarityAndContextAt(pos, e, polarity)._1
    val lambda_pos = HOLPosition.toLambdaPosition(e)(pos)
    lambda_pos.get(e) match {
      case Some(All(_, _)) => pol == Positive
      case Some(Ex(_, _))  => pol == Negative
      case _               => false
    }
  }
}

object CreateSkolemizationProof {

  /**
   * creates a proof F :- skF
   * @param unskolemized the unskolemized formula F
   * @param skolemized the skolemized formula skF
   * @param skVar the variable of the strong quantifier removed
   * @param skTerm the skolem term
   * @param pathToSk the position at which the strong quantifier occurs
   * @param polarity in which polarity we are right now
   * @return
   */
  def apply(unskolemized: FOLFormula, skolemized: FOLFormula, skVar: FOLVar, skTerm: FOLTerm, innerFormula: FOLFormula, pathToSk: HOLPosition, polarity: Polarity): LKProof = {
    if unskolemized == skolemized then
      LogicalAxiom(skolemized)
    if pathToSk.isEmpty then {
      val innerSubstituted = innerFormula.substitute(skVar -> skTerm)
      val axiom = LogicalAxiom(innerSubstituted)
      if polarity == Negative then
        ExistsSkLeftRule(axiom, Ant(0), Ex(skVar, innerFormula), skTerm)
      else
        ForallSkRightRule(axiom, Suc(0), All(skVar, innerFormula), skTerm)
    } else {
      val branch = pathToSk.head
      val remainingBranch = pathToSk.tail
      // polarity swaps on which side the unskolemized and skolemized formula appear (neg: skolemized right, pos: skolemized left)
      def swapPos(a: FOLFormula, b: FOLFormula) = if polarity == Negative then (a, b) else (b, a)

      (unskolemized, skolemized, branch) match {
        case (a @ Neg(f), sa @ Neg(fs), 1) =>
          val rp = apply(f, fs, skVar, skTerm, innerFormula, remainingBranch, !polarity)
          val (b, sb) = swapPos(fs, f) // NegLeftRule needs the auxiliary, not the primary formula
          val p1 = NegLeftRule(rp, sb)
          NegRightRule(p1, b)
        case (a @ And(f, g), sa @ And(fs, _), 1) =>
          val rp = apply(f, fs, skVar, skTerm, innerFormula, remainingBranch, polarity)
          val axiom = LogicalAxiom(g)
          val (b, sb) = swapPos(a, sa)
          val p1 = AndRightRule(rp, axiom, sb)
          AndLeftRule(p1, b)
        case (a @ And(f, g), sa @ And(_, gs), 2) =>
          val axiom = LogicalAxiom(f)
          val rp = apply(g, gs, skVar, skTerm, innerFormula, remainingBranch, polarity)
          val (b, sb) = swapPos(a, sa)
          val p1 = AndRightRule(axiom, rp, sb)
          AndLeftRule(p1, b)
        case (a @ Or(f, g), sa @ Or(fs, _), 1) =>
          val rp = apply(f, fs, skVar, skTerm, innerFormula, remainingBranch, polarity)
          val axiom = LogicalAxiom(g)
          val (b, sb) = swapPos(a, sa)
          val p1 = OrLeftRule(rp, axiom, b)
          OrRightRule(p1, sb)
        case (a @ Or(f, g), sa @ Or(_, gs), 2) =>
          val rp = apply(g, gs, skVar, skTerm, innerFormula, remainingBranch, polarity)
          val axiom = LogicalAxiom(f)
          val (b, sb) = swapPos(a, sa)
          val p1 = OrLeftRule(axiom, rp, b)
          OrRightRule(p1, sb)
        case (a @ Imp(f, g), sa @ Imp(fs, _), 1) =>
          val rp = apply(f, fs, skVar, skTerm, innerFormula, remainingBranch, !polarity)
          val axiom = LogicalAxiom(g)
          val (b, sb) = swapPos(a, sa)
          val p1 = ImpLeftRule(rp, axiom, b)
          ImpRightRule(p1, sb)
        case (a @ Imp(f, g), sa @ Imp(_, gs), 2) =>
          val rp = apply(g, gs, skVar, skTerm, innerFormula, remainingBranch, polarity)
          val axiom = LogicalAxiom(f)
          val (b, sb) = swapPos(a, sa)
          val p1 = ImpLeftRule(axiom, rp, b)
          ImpRightRule(p1, sb)
        case (a @ All(x, f), All(y, fs), 1) =>
          val sa = All(x, fs)
          val rp = apply(f, fs, skVar, skTerm, innerFormula, remainingBranch, polarity)
          val (b, sb) = swapPos(a, sa)
          val p1 = ForallLeftRule(rp, b)
          ForallRightRule(p1, sb)
        case (a @ Ex(x, f), sa @ Ex(y, fs), 1) =>
          val rp = apply(f, fs, skVar, skTerm, innerFormula, remainingBranch, polarity)
          val (b, sb) = swapPos(a, sa)
          val p1 = ExistsRightRule(rp, sb)
          ExistsLeftRule(p1, b)
        case _ =>
          throw IllegalArgumentException(s"Unhandled case ($unskolemized, $skolemized, $pathToSk, $polarity)")
      }
    }
  }
}

trait FileNameResolver {
  def apply(fileName: String): Either[FileNotFound, String]
}

extension [R <: FileNameResolver](r: R) {
  def extend(f: FileNameResolver): FileNameResolver = fileName =>
    boundary { Right(f(fileName).getOrElse { r(fileName).getOrBreak }) }

  def relativeTo(root: os.Path): FileNameResolver = fileName =>
    if Paths.get(fileName).isAbsolute() then r(fileName)
    else r((root / os.RelPath(fileName)).toString)
}

object FileNameResolver {
  val empty: FileNameResolver = fileName => Left(FileNotFound(fileName))
  val absolute: FileNameResolver = fileName => {
    val path =
      if Paths.get(fileName).isAbsolute() then os.Path(fileName)
      else os.Path(fileName, os.pwd)

    if os.exists(path) then Right(os.read(path))
    else Left(FileNotFound(fileName))
  }
  given FileNameResolver = absolute
}

/**
* Checks whether a given input file is a correct TSTP derivation according to the
* rules of the ProoVer competiton 2026. Returns the corresponding SZS status:
* - VerifiedGood: All proof steps are checked to be correct
* - VerifiedBad: There was a mistake in the proof
* - VerifiedUnknown: We could not determine whether the input is a correct proof or not
*
* @param file The input file to check.
* @param resolver The resolver to use for resolving file names.
* @return The [[SzsStatus]] of the check.
*/
def checkTstpDerivation(fileName: String)(using resolver: FileNameResolver): SzsStatus = {
  val result =
    try {
      for
        input <- resolver(fileName)
        inputFile = InputFile.fromString(input)
        derivation <- StructurallyCorrectTstpDerivation.fromInputFile(inputFile)
        _ <- checkDerivationHasRefutation(derivation)
        _ <- checkDerivationHasCorrectFileDirectives(derivation, fileName)
        _ <- checkDerivationHasCorrectStatuses(derivation)
        _ <- checkDerivationHasNoIncorrectInferences(derivation)
      yield ()
    } catch e => Left(UnexpectedException(e))

  result match {
    case Left(reason: VerifiedUnknownReason) => SzsStatus.Unknown(reason)
    case Left(reason: VerifiedBadReason)     => SzsStatus.VerifiedBad(reason)
    case Right(_)                            => SzsStatus.VerifiedGood
  }
}

def checkDerivationHasRefutation(derivation: StructurallyCorrectTstpDerivation): Either[TstpDerivationError, Unit] = {
  if derivation.nonConjectureRootRefutationLabels.isEmpty then
    Left(NoRefutationFound())
  else
    Right(())
}

def checkDerivationHasCorrectStatuses(derivation: StructurallyCorrectTstpDerivation): Either[TstpDerivationError, Unit] = boundary {
  derivation.stepsIterator.foreach {
    case s: ParsedTstpNegatedConjectureStep if !s.hasUnambiguousStatusAmong(Set("cth")) =>
      break(Left(StepWithInvalidStatus(s.name, s.statuses, Set("cth"))))
    case s: ParsedTstpPlainInferenceStep if !s.hasUnambiguousStatusAmong(Set("thm")) =>
      break(Left(StepWithInvalidStatus(s.name, s.statuses, Set("thm"))))
    case s: ParsedTstpSkolemizationStep if !s.hasUnambiguousStatusAmong(Set("esa")) =>
      break(Left(StepWithInvalidStatus(s.name, s.statuses, Set("esa"))))
    case _ =>
  }
  Right(())
}

def checkDerivationHasCorrectFileDirectives(derivation: StructurallyCorrectTstpDerivation, fileName: String)(using resolver: FileNameResolver): Either[TstpDerivationError, Unit] = boundary {
  val parseTptpMemoTable: scala.collection.mutable.Map[String, TptpFile] = scala.collection.mutable.Map.empty
  val innerResolver = resolver.relativeTo(os.Path(fileName) / os.up)
  derivation.stepsIterator.foreach {
    case s: FileSourceStep => {
      val (fileName, label) = (s.problemFile, s.problemFileLabel)
      val tptpFile = parseTptpMemoTable.getOrElseUpdate(
        fileName, {
          val tptpFileContent = innerResolver(fileName).getOrElse {
            break(Left(FileDirectiveFileNotFound(s.name, fileName)))
          }
          try TptpImporter.loadWithoutIncludes(InputFile.fromString(tptpFileContent))
          catch {
            case _: IllegalArgumentException =>
              break(Left(FileDirectiveInvalidSyntax(s.name, fileName)))
          }
        }
      )

      val fileDirectiveFormulas = tptpFile.inputs.collect {
        case a: AnnotatedFormula if a.name == label => a
      }
      val fileDirectiveFormula = fileDirectiveFormulas match {
        case Seq() =>
          break(Left(FileDirectiveFileDoesNotHaveLabel(s.name, fileName, label)))
        case Seq(_, _, _*) =>
          break(Left(FileDirectiveFileHasMultipleFormulasWithSameLabel(s.name, fileName, label)))
        case Seq(a @ AnnotatedFormula(language, name, "hypothesis", formula, annotations)) =>
          AnnotatedFormula(language, name, "axiom", formula, annotations) // hypothesis is a synonym for axiom
        case Seq(a) => a
      }

      if fileDirectiveFormula.role != s.role then {
        break(Left(FileDirectiveStepDoesNotMatchRole(s.name, fileName, label, s.role, fileDirectiveFormula.role)))
      }

      if !fileDirectiveFormula.formula.alphaEquals(s.formula) then {
        break(Left(FileDirectiveFormulaNotAlphaEquivalentToClaimedFormula(
          s.name,
          fileName,
          label,
          fileDirectiveFormula.formula,
          s.formula
        )))
      }
    }
    case _ =>
  }
  Right(())
}

extension (annotations: Option[Annotations]) {
  def hasUnambiguousStatusAmong(statuses: Set[String]): Boolean = boundary {
    val ann = annotations.getOrElse { break(false) }
    val inferenceSource = ann.source.asInferenceOption.getOrElse { break(false) }
    val inferenceStatus = inferenceSource.statuses.singleOption.getOrElse { break(false) }

    statuses.contains(inferenceStatus)
  }
}

extension (step: ParsedTstpDerivationStep) {
  def hasUnambiguousStatusAmong(statuses: Set[String]): Boolean = boundary {
    step.annotationsOption.hasUnambiguousStatusAmong(statuses)
  }
}

extension (gt: GeneralTerm) {
  def asStatus: Option[String] = gt match {
    case TptpTerm("status", TptpTerm(value)) => Some(value)
    case _                                   => None
  }
}

extension (usefulInfo: Seq[GeneralTerm]) {
  def statusSet: Set[String] =
    usefulInfo.flatMap(_.asStatus).toSet
}

extension (inference: Source.Inference) {
  def statuses: Set[String] =
    inference.usefulInfo.statusSet
}

extension (step: ParsedTstpPlainInferenceStep) {
  def statuses: Set[String] = step.source.statuses
}

extension (step: ParsedTstpNegatedConjectureStep) {
  def statuses: Set[String] = step.source.statuses
}

extension (step: ParsedTstpSkolemizationStep) {
  def statuses: Set[String] = step.source.statuses
}

extension (annotatedFormula: AnnotatedFormula) {
  def parentLabels: Seq[String] = boundary {
    val annotations = annotatedFormula.annotations.getOrElse { break(Seq.empty) }
    annotations.source.parentLabels
  }
}

extension (source: Source) {
  def asInferenceOption: Option[Source.Inference] = source match {
    case s @ Source.Inference(rule, usefulInfo, parents) => Some(s)
    case _                                               => None
  }

  def parentLabels: Seq[String] = source match {
    case Source.Name(name)                                => Seq(name)
    case Source.Inference(_, _, parents)                  => parents.flatMap(_.source.parentLabels)
    case Source.Internal(_, _, parents)                   => parents.flatMap(_.source.parentLabels)
    case Source.File(_, _)                                => Seq.empty // for now we treat file sources as axioms that don't have parents
    case Source.Theory(_, _)                              => Seq.empty
    case Source.Creator(_, _, parents)                    => parents.flatMap(_.source.parentLabels)
    case Source.Unknown                                   => Seq.empty
    case Source.List(sources)                             => sources.flatMap(_.parentLabels)
    case Source.General(GeneralColon(TptpTerm(label), _)) => Seq(label)
    case Source.General(TptpTerm(dagSource))              => Seq(dagSource)
    case Source.General(term)                             => throw IllegalArgumentException(s"parent must be a simple term. got: $term")
  }
}

extension (step: ParsedTstpDerivationStep) {
  def annotationsOption: Option[Annotations] = step match {
    case s: ParsedTstpConjectureStep =>
      s.annotationsOption
    case s: ParsedTstpAxiomStep =>
      s.annotationsOption
    case s: ParsedTstpPlainInferenceStep =>
      Some(s.annotations)
    case s: ParsedTstpNegatedConjectureStep =>
      Some(s.annotations)
    case s: ParsedTstpSkolemizationStep =>
      Some(s.annotations)
  }
}

extension [T](a: IterableOnce[T]) {
  def single: T = a.iterator.take(2).toSeq match {
    case Seq()  => throw new NoSuchElementException
    case Seq(x) => x
    case _      => throw new IllegalArgumentException("Expected at most one element, got " + a)
  }

  def singleOption: Option[T] = a.iterator.take(2).toSeq match {
    case Seq()  => None
    case Seq(x) => Some(x)
    case _      => None
  }
}

case class InputSyntaxError(
    cause: IllegalArgumentException
) extends VerifiedUnknownReason {
  override def message: String = cause.getMessage
}

case class DistinctFormulasWithSameName(
    label: String
) extends VerifiedBadReason {
  override def message: String = s"there are multiple distinct formulas with the same name: $label"
}

case class InferenceCycle() extends VerifiedBadReason {
  def message: String = "inference cycle detected"
}

case class StepWithInvalidStatus(
    stepName: String,
    actualStatuses: Iterable[String],
    validStatuses: Iterable[String]
) extends VerifiedBadReason {
  override def message: String = s"$stepName has invalid statuses ${actualStatuses.mkString(", ")}. Expected one of ${validStatuses.mkString(", ")}"
}

case class StepWithInvalidInferenceRule(
    stepName: String,
    actualInferenceName: String,
    expectedInferenceName: String
) extends VerifiedBadReason {
  override def message: String = s"$stepName has invalid inference name '$actualInferenceName'. Expected '$expectedInferenceName'"
}

case class NegatedConjectureStepWithNonConjectureParent(
    stepName: String
) extends VerifiedBadReason {
  def message: String = s"step with name $stepName has a non-conjecture parent"
}

case class NegatedConjectureWithoutParent(
    stepName: String
) extends VerifiedBadReason {
  def message: String = s"negated conjecture step with name $stepName has no parent"
}

case class NegatedConjectureWithMultipleDistinctParents() extends VerifiedBadReason {
  def message: String = "got negated conjecture with multiple distinct parents"
}

case class PlainInferenceWithConjectureParent(
    step: ParsedTstpPlainInferenceStep
) extends VerifiedBadReason {
  def message: String = s"plain inference step with name ${step.name} has a conjecture parent"
}

case class PlainInferenceWithoutSource(
    stepName: String
) extends VerifiedBadReason {
  def message: String = s"plain inference step with name $stepName has no source"
}

case class IncorrectInference(
    stepName: String
) extends VerifiedBadReason {
  def message: String = s"inference step with name $stepName is incorrect"
}

case class IncorrectSkolemization(
    reason: IncorrectSkolemizationReason
) extends VerifiedBadReason {
  def message: String = reason.message
}

case class NonConstantSkolemTerm(
    stepName: String,
    term: FOLVar
) extends VerifiedBadReason {
  def message: String = s"step $stepName: skolem term $term is not a constant, but a variable"
}

case class SkolemizationStepWithoutParent(
    stepName: String
) extends VerifiedBadReason {
  def message: String = s"skolemization inference with name $stepName has no parent"
}

case class SkolemizationStepWithMultipleParents(
    stepName: String,
    parents: Seq[String]
) extends VerifiedBadReason {
  def message: String = s"skolemization inference with name $stepName has multiple parents ${parents.mkString(", ")}"
}

case class NonExistentStep(
    stepName: String
) extends VerifiedBadReason {
  def message: String = s"step with name $stepName does not exist"
}

sealed trait IncorrectSkolemizationReason {
  def message: String
}

case class NoExistentialQuantifierAfterRootUniversalBlock(
    stepName: String,
    claimedBoundVariable: FOLVar,
    innerFormula: FOLFormula,
    parentFormula: FOLFormula
) extends IncorrectSkolemizationReason {
  def message: String = s"skolemization step $stepName claims to skolemize bound variable $claimedBoundVariable, but there is no existential quantifier following after the outermost universal quantifiers. got $innerFormula inside universal quantifier block of parent formula $parentFormula"
}

case class BoundVariableMismatch(
    stepName: String,
    claimedBoundVariable: FOLVar,
    actualBoundVariable: FOLVar,
    parentFormula: FOLFormula
) extends IncorrectSkolemizationReason {
  def message: String = s"skolemization step $stepName claims to skolemize bound variable $claimedBoundVariable, but the actual outer most existential variable in $parentFormula is $actualBoundVariable"
}

case class ContextVariableMismatch(
    stepName: String,
    claimedContextVariables: Seq[FOLVar],
    actualOuterSkolemizationContextVariables: Seq[FOLVar],
    actualInnerSkolemizationContextVariables: Seq[FOLVar],
    claimedBoundVariable: FOLVar,
    parentFormula: FOLFormula
) extends IncorrectSkolemizationReason {
  def message: String = s"skolemization step $stepName claims to have context variables $claimedContextVariables, but this neither matches the actual outer skolemization context variables ($actualOuterSkolemizationContextVariables) nor the inner skolemization context variables ($actualInnerSkolemizationContextVariables) for $claimedBoundVariable in $parentFormula"
}

case class FormulaMismatch(
    stepName: String,
    claimedSkolemizedFormula: FOLFormula,
    claimedBoundVariable: FOLVar,
    claimedSkolemTerm: FOLTerm,
    expectedSkolemizedFormula: FOLFormula,
    parentFormula: FOLFormula
) extends IncorrectSkolemizationReason {
  def message: String = s"skolemization step $stepName claims to skolemize formula $parentFormula by replacing $claimedBoundVariable with $claimedSkolemTerm which should result in $expectedSkolemizedFormula but the given formula is $claimedSkolemizedFormula"
}

case class MultipleIncompatibleSkolemDefinitionsOfSameSymbol(
    skolemSymbol: String,
    stepDefinitions: Map[String, VerifiedSkolemization]
) extends IncorrectSkolemizationReason {
  def message: String = s"skolem symbol $skolemSymbol is introduced multiple times with conflicting definitions: ${stepDefinitions.map { case (step, skolemization) => s"in $step defined as skolem symbol ${skolemization.skolemSymbol} with ${skolemization.skolemDefinition}" }.mkString("; ")}"
}

case class SkolemSymbolIsAConstantExistingInTheInput(
    inputStepName: String,
    skolemizationStepName: String,
    const: Const
) extends IncorrectSkolemizationReason {
  def message: String = s"skolemization step $skolemizationStepName introduces skolem symbol $const that is already used in the input in step $inputStepName"
}

case class NonRectifiedFormula(
    stepName: String,
    formula: FOLFormula
) extends IncorrectSkolemizationReason {
  def message: String = s"skolemization step $stepName has non-rectified parent formula $formula (contains different quantifiers with the same bound variable)"
}

case class SkolemizationStepWithNewSymbolDifferingFromSkolemizeTerm(
    stepName: String
) extends VerifiedBadReason {
  def message: String = s"skolemization step with name $stepName has differing skolem terms"
}

case class SkolemizationStepWithoutNewSymbols(
    stepName: String
) extends VerifiedBadReason {
  def message: String = s"skolemization step with name $stepName has no new symbols"
}

case class SkolemizationStepWithoutBinding(
    stepName: String
) extends VerifiedBadReason {
  def message: String = s"skolemization step with name $stepName has no skolemize(_,_) binding"
}

case class CannotHandleIncludeDirectives() extends VerifiedUnknownReason {
  def message: String = "cannot handle include directives"
}

case class CannotHandleInput(stepName: String, reason: String) extends VerifiedUnknownReason {
  def message: String = s"cannot handle input step with name $stepName: $reason"
}

case class NoRefutationFound() extends VerifiedBadReason {
  def message: String = "no refutation found as there is no unique $false formula in the derivation"
}

case class AmbiguousRefutationLabelsFound(labels: Seq[String]) extends VerifiedBadReason {
  def message: String = s"no refutation found as there are multiple $$false formulas in the derivation: ${labels.mkString(", ")}"
}

case class UnexpectedInput(message: String) extends VerifiedUnknownReason

case class NoStrongQuantifierFittingSkolemization(stepName: String, inputFormula: FOLFormula, skolemizedFormula: FOLFormula, skVar: FOLVar, skTerm: FOLTerm)
    extends IncorrectSkolemizationReason {
  def message: String = s"could not find a strong quantifier s.t. replacing $skVar with $skTerm transforms $inputFormula into $skolemizedFormula!"
}

case class MultipleStrongQuantifiersFittingSkolemization(stepName: String, inputFormula: FOLFormula, skolemizedFormula: FOLFormula, skVar: FOLVar, skTerm: FOLTerm)
    extends IncorrectSkolemizationReason {
  def message: String = s"could find multiple (non-unique) strong quantifiers s.t. replacing $skVar with $skTerm transforms $inputFormula into $skolemizedFormula!"
}

sealed trait FileDirectiveError extends VerifiedBadReason
case class SourceMissing(stepName: String) extends FileDirectiveError {
  override def message: String = s"step $stepName is missing a source"
}

case class FileDirectiveMissing(stepName: String) extends FileDirectiveError {
  override def message: String = s"step $stepName is missing a file directive"
}

case class FileDirectiveLabelMissing(stepName: String) extends FileDirectiveError {
  override def message: String = s"step $stepName is missing a file directive label"
}

case class FileDirectiveFileNotFound(stepName: String, fileName: String) extends FileDirectiveError {
  override def message: String = s"step $stepName has a file source (${fileName}) that could not be found"
}

case class FileDirectiveInvalidSyntax(stepName: String, fileName: String) extends FileDirectiveError {
  override def message: String = s"step $stepName has a file source (${fileName}) with invalid TPTP syntax"
}

case class FileDirectiveFileDoesNotHaveLabel(
    stepName: String,
    fileName: String,
    label: String
) extends FileDirectiveError {
  override def message: String = s"step $stepName has a file source (${fileName}) that does not have the label '$label'"
}

case class FileDirectiveFileHasMultipleFormulasWithSameLabel(
    stepName: String,
    fileName: String,
    label: String
) extends FileDirectiveError {
  override def message: String = s"step $stepName has a file source (${fileName}) that has multiple distinct formulas with the same label '$label'"
}

case class FileDirectiveStepDoesNotMatchRole(
    stepName: String,
    fileName: String,
    label: String,
    expectedRole: String,
    actualRole: String
) extends FileDirectiveError {
  override def message: String = s"step ${stepName} has a file source (${fileName}) that points to a formula with name ${label} that does not have the same role as the step. expected: ${expectedRole}, actual: ${actualRole}"
}

case class FileDirectiveFormulaNotAlphaEquivalentToClaimedFormula(
    stepName: String,
    fileName: String,
    label: String,
    expected: Formula,
    actual: Formula
) extends FileDirectiveError {
  override def message: String = s"step ${stepName} has a file source (${fileName}) that points to a formula with name ${label} that is not alpha-equivalent to the claimed formula. expected: ${expected}, actual: ${actual}"
}

case class FileNotFound(fileName: String) extends VerifiedUnknownReason {
  override def message: String = s"file not found: $fileName"
}

case class UnexpectedException(e: Throwable) extends VerifiedUnknownReason {
  override def message: String = s"unexpected exception: ${e.getMessage}"
}

case class StepsWithOverloadedSymbols(symbolName: String, steps: Set[ParsedTstpDerivationStep]) extends VerifiedUnknownReason {
  override def message: String = s"cannot handle overloaded symbols. symbol $symbolName occurs overloaded in the following steps: ${steps.map(_.name).mkString(", ")}"
}
