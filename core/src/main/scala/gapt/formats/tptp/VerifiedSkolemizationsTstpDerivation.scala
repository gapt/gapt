package gapt.formats.tptp.check

import gapt.expr.{Abs, Const, Expr, Var}
import gapt.expr.formula.*
import gapt.expr.formula.fol.{FOLAtom, FOLFormula, FOLFunctionConst, FOLTerm, FOLVar}
import gapt.expr.formula.hol.HOLPosition
import gapt.expr.given
import gapt.expr.substitute
import gapt.expr.util.{constants, freeVariables}
import gapt.formats.tptp.*
import gapt.formats.tptp.check.FindSkolemizableInstance.QuantifierType
import gapt.logic.Polarity
import gapt.logic.Polarity.{Negative, Positive}
import gapt.proofs.{Ant, Suc}
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.*
import gapt.utils.getOrBreak

import scala.util.boundary
import scala.util.boundary.Label
import boundary.break
import scala.collection.SeqMap

/**
 * A structurally correct TSTP derivation for which every skolemization step has
 * been checked, and whose Skolem definitions are globally compatible and fresh
 * with respect to the input formulas.
 */
final class VerifiedSkolemizationsTstpDerivation private (
    val structurallyCorrect: StructurallyCorrectTstpDerivation,
    private val verifiedSkolemizationsByStepName: SeqMap[String, VerifiedSkolemization]
) {
  private[check] def verifiedSkolemization(stepName: String): Option[VerifiedSkolemization] =
    verifiedSkolemizationsByStepName.get(stepName)

  private[check] def verifiedSkolemizations: Iterable[VerifiedSkolemization] =
    verifiedSkolemizationsByStepName.values

}

object VerifiedSkolemizationsTstpDerivation {
  def fromStructurallyCorrect(
      derivation: StructurallyCorrectTstpDerivation
  ): Either[IncorrectSkolemization, VerifiedSkolemizationsTstpDerivation] =
    checkSkolemSymbolsAreNotOverloaded(derivation).flatMap { _ =>
      fromNormalizedAndFresh(StructurallyCorrectTstpDerivation.deoverloadSymbols(derivation))
    }

  private[check] def fromNormalizedAndFresh(
      derivation: StructurallyCorrectTstpDerivation
  ): Either[IncorrectSkolemization, VerifiedSkolemizationsTstpDerivation] = boundary {
    val verifiedSkolemizationsInSourceOrder = SeqMap.from(derivation.stepsInSourceOrderIterator.collect {
      case step: ParsedTstpSkolemizationStep =>
        val parentFormula = derivation.get(step.parent).get.formula
        val locallyCorrectSkolemization =
          VerifiedSkolemization.fromTstpSkolemizationStepAndParentFormula(step, parentFormula).getOrBreak

        step.name -> locallyCorrectSkolemization
    })

    ensureCompatibleSkolemDefinitions(verifiedSkolemizationsInSourceOrder).getOrBreak
    Right(new VerifiedSkolemizationsTstpDerivation(derivation, verifiedSkolemizationsInSourceOrder))
  }
}

private[check] def checkSkolemSymbolsAreNotOverloaded(
    derivation: StructurallyCorrectTstpDerivation
): Either[IncorrectSkolemization, Unit] = boundary {
  val declaredSkolemSymbols = SeqMap.from(derivation.stepsInSourceOrderIterator.collect {
    case step: ParsedTstpSkolemizationStep => step.name -> step.newSkolemSymbol
  })

  val skolemSymbolsByName = declaredSkolemSymbols.groupMap(_._2.name)(_._2)
  declaredSkolemSymbols.foreach { (_, skolemSymbol) =>
    val symbols = skolemSymbolsByName(skolemSymbol.name)
    if symbols.toSet.size > 1 then {
      reportIncorrectSkolemization(
        SkolemSymbolWithDifferentArities(
          skolemSymbol.name,
          SeqMap.from(declaredSkolemSymbols.filter((_, symbol) => symbol.name == skolemSymbol.name))
        )
      )
    }
  }

  declaredSkolemSymbols.foreach { (skolemizationStepName, skolemSymbol) =>
    derivation.stepsInSourceOrderIterator.foreach { step =>
      constants.all(step.formula).toSeq.sortBy(_.toString).filter(_.name == skolemSymbol.name).foreach { symbol =>
        if symbol != skolemSymbol then {
          reportIncorrectSkolemization(
            SkolemSymbolWithDifferentArity(
              skolemizationStepName,
              skolemSymbol,
              step.name,
              symbol
            )
          )
        }
      }
    }
  }

  val inputSymbols = derivation.stepsInSourceOrderIterator.collect {
    case step: ParsedTstpAxiomStep      => step.name -> constants.nonLogical(step.formula)
    case step: ParsedTstpConjectureStep => step.name -> constants.nonLogical(step.formula)
  }
  inputSymbols.foreach { (inputStepName, symbols) =>
    symbols.toSeq.sortBy(_.toString).foreach { symbol =>
      declaredSkolemSymbols.find((_, skolemSymbol) => skolemSymbol.name == symbol.name).foreach {
        (skolemizationStepName, _) =>
          reportIncorrectSkolemization(
            SkolemSymbolIsAConstantExistingInTheInput(inputStepName, skolemizationStepName, symbol)
          )
      }
    }
  }

  Right(())
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
    skolemizationsInSourceOrder: SeqMap[String, VerifiedSkolemization]
): Either[IncorrectSkolemization, Unit] = boundary {
  val skolemizationsBySkolemSymbolName =
    skolemizationsInSourceOrder.groupBy((_, skolemization) => skolemization.skolemSymbol.name)

  skolemizationsInSourceOrder.foreachEntry { (stepName, skolemization) =>
    val definitionsByStepName = skolemizationsBySkolemSymbolName(skolemization.skolemSymbol.name)

    if definitionsByStepName.size > 1 then {
      // TPTP requires each Skolem symbol to be introduced by exactly one step.
      // Therefore, repeated declarations are incompatible even if their inferred
      // definitions are syntactically identical.
      reportIncorrectSkolemization(MultipleIncompatibleSkolemDefinitionsOfSameSymbol(skolemization.skolemSymbol.name, definitionsByStepName))
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
