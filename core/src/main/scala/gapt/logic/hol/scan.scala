package gapt.logic.hol

import gapt.expr._
import gapt.proofs.HOLClause
import gapt.proofs.FOLClause
import gapt.proofs.SequentIndex
import gapt.expr.util.rename
import gapt.expr.util.freeVariables
import gapt.expr.subst.Substitution
import gapt.expr.formula.Atom
import gapt.expr.formula.hol.freeHOVariables
import gapt.expr.formula.fol.FOLVar
import gapt.proofs.RichFormulaSequent
import gapt.expr.util.syntacticMGU
import gapt.expr.formula.Eq
import gapt.proofs.Ant
import gapt.expr.subst.FOLSubstitution
import gapt.expr.formula.fol.FOLTerm
import gapt.proofs.HOLSequent
import gapt.expr.ty.Ti
import gapt.logic.Polarity
import gapt.logic.hol.AndOr
import gapt.expr.formula.Formula
import gapt.expr.formula.Top
import gapt.expr.formula.And
import gapt.expr.formula.Or
import gapt.expr.formula.All
import gapt.expr.formula.Ex
import gapt.expr.BetaReduction.betaNormalize
import gapt.expr.Abs.Block
import gapt.expr.ty.FunctionType
import gapt.expr.ty.To
import gapt.expr.formula.constants.BottomC
import gapt.logic.hol.wdls.simplify
import gapt.expr.formula.constants.TopC
import gapt.expr.preExpr.Type
import gapt.utils.NameGenerator
import gapt.expr.ty.Ty
import gapt.formats.leancop.LeanCoPParser.inferences
import gapt.logic.clauseSubsumption
import gapt.expr.subst.PreSubstitution
import gapt.proofs.Suc
import gapt.proofs.Sequent
import scala.collection.immutable.HashSet
import gapt.provers.escargot.Escargot
import gapt.expr.formula.Iff
import gapt.formats.leancop.LeanCoP21Parser.clause
import gapt.logic.hol.PredicateEliminationProblem
import gapt.logic.hol.ClauseSetPredicateEliminationProblem

object scan {
  def apply(
      input: ClauseSetPredicateEliminationProblem,
      oneSidedOnly: Boolean = true,
      allowResolutionOnBaseLiterals: Boolean = false,
      derivationLimit: Option[Int] = Some(100),
      attemptLimit: Option[Int] = Some(10)
  ): Either[Iterator[Derivation], Derivation] = {
    val baseIterator = scan.derivationsFrom(
      input = input,
      oneSidedOnly = oneSidedOnly,
      allowResolutionOnBaseLiterals = allowResolutionOnBaseLiterals,
      derivationLimit = derivationLimit
    )
    val iterator = attemptLimit.map(l => baseIterator.take(l)).getOrElse(baseIterator)

    val successfulDerivation = iterator
      .collect { case Right(value) => value }
      .nextOption()
    successfulDerivation match
      case None             => Left(iterator.map(_.merge))
      case Some(derivation) => Right(derivation)
  }

  def derivationsFrom(
      input: ClauseSetPredicateEliminationProblem,
      oneSidedOnly: Boolean = true,
      allowResolutionOnBaseLiterals: Boolean = false,
      derivationLimit: Option[Int] = Some(100)
  ): Iterator[Either[Derivation, Derivation]] = {
    assert(derivationLimit.isEmpty || derivationLimit.get >= 0, "derivation limit must be non-negative")
    val states = saturateByPurification(State.initialFrom(
      input,
      derivationLimit = derivationLimit,
      oneSidedOnly = oneSidedOnly,
      allowResolutionOnBaseLiterals = allowResolutionOnBaseLiterals
    ))
    states.map(state => state.map(_.derivation).left.map(_.derivation))
  }

  case class PointedClause(clause: HOLClause, index: SequentIndex):
    def atom = clause(index)
    def args = atom match
      case Atom(_, args) => args

    def hoVar: VarOrConst = atom match
      case Atom(v @ VarOrConst(_, _, _), _) => v

    def isVar: Boolean = hoVar match {
      case _: Var => true
      case _      => false
    }

  enum DerivationStep:
    case ConstraintResolution(left: PointedClause, right: PointedClause)
    case ConstraintFactoring(clause: HOLClause, leftIndex: SequentIndex, rightIndex: SequentIndex)
    case PurifiedClauseDeletion(candidate: PointedClause)
    case TautologyDeletion(tautology: HOLClause)
    case SubsumptionDeletion(subsumer: HOLClause, subsumee: HOLClause, substitution: FOLSubstitution)
    case ConstraintElimination(clause: HOLClause, index: SequentIndex, substitution: FOLSubstitution)
    case ExtendendPurityDeletion(hoVar: Var, polarity: gapt.logic.Polarity)

    def addedRemovedClauses(clauses: Set[HOLClause]): (Set[HOLClause], Set[HOLClause]) =
      this match
        case ConstraintResolution(left, right)                     => (Set(constraintResolvent(left, right)), Set.empty)
        case f: ConstraintFactoring                                => (Set(factor(f)), Set.empty)
        case PurifiedClauseDeletion(candidate)                     => (Set.empty, Set(candidate.clause))
        case SubsumptionDeletion(subsumer, subsumee, substitution) => (Set.empty, Set(subsumee))
        case TautologyDeletion(clause)                             => (Set.empty, Set(clause))
        case ConstraintElimination(clause, index, substitution)    => (Set(substitution(clause.delete(index)).map { case a: Atom => a }.distinct), Set(clause))
        case ExtendendPurityDeletion(hoVar, polarity) => {
          val removed = clauses.filter(c =>
            c.exists {
              case Atom(v: Var, _) if v == hoVar => true
              case _                             => false
            }
          )
          (Set.empty, removed)
        }

    def apply(clauses: Set[HOLClause]): Set[HOLClause] =
      val (added, removed) = addedRemovedClauses(clauses)
      (clauses ++ added) -- removed

  def factor(factoring: DerivationStep.ConstraintFactoring): HOLClause = {
    val DerivationStep.ConstraintFactoring(clause, leftIndex, rightIndex) = factoring
    val Atom(_, leftArgs) = clause(leftIndex): @unchecked
    val Atom(_, rightArgs) = clause(rightIndex): @unchecked
    val constraints = leftArgs.zip(rightArgs).map(Eq(_, _))
    (clause.delete(rightIndex) ++ HOLClause(constraints, Seq.empty)).distinct
  }

  def isFactorOf(clause: HOLClause, other: HOLClause): Boolean = {
    factoringInferences(other).exists(i => factor(i) == clause)
  }

  def factoringInferences(clause: HOLClause): Set[DerivationStep.ConstraintFactoring] = {
    clause.succedent.zipWithIndex.combinations(2).flatMap {
      case Seq(left @ (Atom(leftHead, _), _: Int), right @ (Atom(rightHead, _), _: Int)) if leftHead == rightHead => Some((left, right))
      case _                                                                                                      => None
    }.map[DerivationStep.ConstraintFactoring] {
      case ((_, leftIndex), (_, rightIndex)) => DerivationStep.ConstraintFactoring(clause, Suc(leftIndex), Suc(rightIndex))
    }.toSet
  }

  case class Derivation(initialPep: ClauseSetPredicateEliminationProblem, inferences: List[DerivationStep]):
    def tail: Derivation = inferences match
      case head :: next => Derivation(
          ClauseSetPredicateEliminationProblem(
            initialPep.variablesToEliminate,
            head(initialPep.clauses)
          ),
          next
        )
      case Nil => throw UnsupportedOperationException("tail of empty derivation")

    def conclusion: Set[HOLClause] = inferences match
      case Nil => initialPep.clauses
      case head :: next => Derivation(
          ClauseSetPredicateEliminationProblem(
            initialPep.variablesToEliminate,
            head(initialPep.clauses)
          ),
          next
        ).conclusion

  object Derivation:
    def emptyFrom(initialPep: ClauseSetPredicateEliminationProblem): Derivation = Derivation(initialPep, List.empty)

  case class State(
      activeClauses: Set[HOLClause],
      derivation: Derivation,
      derivationLimit: Option[Int],
      oneSidedOnly: Boolean,
      allowResolutionOnBaseLiterals: Boolean
  ):
    def variablesToEliminate = derivation.initialPep.variablesToEliminate
    def isEliminated = activeClauses.forall(c => freeHOVariables(c.toFormula).intersect(variablesToEliminate.toSet).isEmpty)
    def isPointedClauseWithEliminationVariable(pointedClause: PointedClause) =
      pointedClause.isVar && variablesToEliminate.contains(pointedClause.hoVar.asInstanceOf[Var])

  object State:
    def initialFrom(
        input: ClauseSetPredicateEliminationProblem,
        derivationLimit: Option[Int],
        oneSidedOnly: Boolean,
        allowResolutionOnBaseLiterals: Boolean
    ): State =
      State(
        input.clauses,
        Derivation.emptyFrom(input),
        derivationLimit,
        oneSidedOnly,
        allowResolutionOnBaseLiterals
      )

  def subsumptionSubstitution(subsumer: HOLClause, subsumee: HOLClause): Option[FOLSubstitution] = {
    val subsumerHoVarsAsConsts = subsumer.map { case Atom(VarOrConst(v, ty, tys), args) => Atom(Const(v, ty, tys), args) }
    val subsumeeHoVarsAsConsts = subsumee.map { case Atom(VarOrConst(v, ty, tys), args) => Atom(Const(v, ty, tys), args) }
    clauseSubsumption(subsumerHoVarsAsConsts, subsumeeHoVarsAsConsts, multisetSubsumption = true).map(_.asFOLSubstitution)
  }

  def isRedundant(clauses: Set[HOLClause], clause: HOLClause): Boolean = {
    val eliminatedConstraints = eliminateConstraints(clause, Set.empty)
    clause.isTaut
    || clauses.exists(c => subsumptionSubstitution(c, clause).isDefined)
    || eliminatedConstraints.isTaut
    || clauses.exists(c => subsumptionSubstitution(c, eliminatedConstraints).isDefined)
  }

  def nextInference(state: State): Seq[Seq[DerivationStep]] = {
    val extendedPurityDeletion = extendedPurityDeletionStep(state)
    val redundancyElimination = redundancyStep(state)

    // do factoring
    val factoring: Option[DerivationStep.ConstraintFactoring] = state.activeClauses.flatMap(factoringInferences).filter {
      case f => !isRedundant(state.activeClauses, factor(f))
    }.headOption

    // check for purification
    val purifications: Seq[DerivationStep.PurifiedClauseDeletion] = pointedClauses(state.activeClauses).filter { p =>
      state.isPointedClauseWithEliminationVariable(p)
    }.flatMap[DerivationStep.PurifiedClauseDeletion] { rc =>
      val hoVar @ Var(_, _) = rc.hoVar: @unchecked
      val allFactorsRedundant = factoringInferences(rc.clause).forall {
        case inference: DerivationStep.ConstraintFactoring => isRedundant(state.activeClauses, factor(inference))
      }
      val allResolventsRedundant = resolutionInferences(state.activeClauses - rc.clause, rc).forall {
        case DerivationStep.ConstraintResolution(left, right) => isRedundant(state.activeClauses, constraintResolvent(left, right))
      }
      val isFactor = state.activeClauses.exists(c => isFactorOf(rc.clause, c))
      if !isFactor && allFactorsRedundant && allResolventsRedundant
      then Some(DerivationStep.PurifiedClauseDeletion(rc))
      else None
    }.toSeq

    val singleInference = extendedPurityDeletion.orElse(redundancyElimination).orElse(factoring)

    val (oneSidedPurifications, mixedPurifications) = purifications.partition(i => isOneSided(i.candidate))

    val activePointedClauseCandidates = state.activeClauses
      .flatMap(c => pointedClauses(c))
      .filter(p => state.allowResolutionOnBaseLiterals || state.isPointedClauseWithEliminationVariable(p))
      .filter(p => (!state.oneSidedOnly || isOneSided(p)) && nonRedundantResolutionInferences(state.activeClauses, p).nonEmpty)

    val resolutionPossibilities: Seq[Seq[DerivationStep.ConstraintResolution]] = activePointedClauseCandidates.toSeq.map { candidate =>
      nonRedundantResolutionInferences(state.activeClauses, candidate)
    }

    if singleInference.isDefined then Seq(singleInference.toSeq)
    else if singleInference.isEmpty && !oneSidedPurifications.isEmpty then
      oneSidedPurifications.map(Seq(_))
    else
      resolutionPossibilities
  }

  def nonRedundantResolutionInferences(clauses: Set[HOLClause], candidate: PointedClause) = {
    resolutionInferences(clauses - candidate.clause, candidate).filter {
      case DerivationStep.ConstraintResolution(left, right) => !isRedundant(clauses, constraintResolvent(left, right))
    }.toSeq
  }

  def isOneSided(pointedClause: PointedClause): Boolean = {
    pointedClause.clause.cedent(!pointedClause.index.polarity).forall {
      case Atom(v: VarOrConst, _) => v != pointedClause.hoVar
      case _                      => true
    }
  }

  def pointedClauses(clause: HOLClause): Set[PointedClause] = {
    clause.indices.map(PointedClause(clause, _)).toSet
  }

  def pointedClauses(clauses: Set[HOLClause]): Set[PointedClause] = {
    clauses.flatMap(pointedClauses)
  }

  def resolutionInferences(clauses: Set[HOLClause], resolutionCandidate: PointedClause): Set[DerivationStep.ConstraintResolution] = {
    pointedClauses(clauses).filter {
      rc => rc.hoVar == resolutionCandidate.hoVar && rc.index.polarity == !resolutionCandidate.index.polarity
    }.map(rc => DerivationStep.ConstraintResolution(resolutionCandidate, rc))
  }

  def saturate(state: State): Iterator[Either[State, State]] = {
    if state.isEliminated then Iterator(Right(state))
    else
      val possibilities = nextInference(state)
      assert(possibilities.nonEmpty, s"nextInference returned no possibilities, even though state is not eliminated: $state")
      possibilities.iterator.flatMap { inferences =>
        assert(inferences.nonEmpty, s"nextInference returned possibility with no inferences, even though state is not eliminated: $state")
        applyDerivationSteps(state, inferences) match
          case l @ Left(_)  => Iterator(l)
          case Right(state) => saturate(state)
      }
  }

  def purificationCandidates(state: State): Iterator[PointedClause] = {
    val (oneSidedCandidates, mixedCandidates) = pointedClauses(state.activeClauses)
      .filter { p =>
        state.isPointedClauseWithEliminationVariable(p) ||
        (state.allowResolutionOnBaseLiterals && nonRedundantResolutionInferences(state.activeClauses - p.clause, p).nonEmpty)
      }
      .partition(isOneSided)
    if state.oneSidedOnly && oneSidedCandidates.isEmpty then {
      println(s"State ${state} is not eliminated, but has no one-sided purification candidates")
      Iterator.empty
    } else {
      val candidates = if state.oneSidedOnly then oneSidedCandidates else (oneSidedCandidates ++ mixedCandidates)
      candidates.iterator
    }
  }

  def saturateByPurification(state: State): Iterator[Either[State, State]] = {
    if state.isEliminated then Iterator(Right(state))
    else {
      val stateAfterRedundancyElimination = eliminateRedundancies(state) match
        case l @ Left(_)  => return Iterator(l)
        case Right(value) => value

      val extendedPurityDeletion = extendedPurityDeletionStep(stateAfterRedundancyElimination)
      val statesAfterExtendedPurityDeletion = extendedPurityDeletion.map(s => applyDerivationSteps(stateAfterRedundancyElimination, Seq(s))).iterator

      val statesAfterPurifications =
        for
          stateAfterFactors <- addFactors(stateAfterRedundancyElimination).flatMap(eliminateRedundancies)
          candidates = purificationCandidates(stateAfterFactors)
        yield {
          candidates.map(p =>
            val purifiedState = purifyPointedClause(stateAfterFactors, p)
            purifiedState.flatMap { state =>
              if !state.isPointedClauseWithEliminationVariable(p) then
                Right(state)
              else
                applyDerivationSteps(state, Seq(DerivationStep.PurifiedClauseDeletion(p)))
            }
          )
        }

      val purificationStates = statesAfterPurifications.left.map(l => Iterator(Left(l))).merge
      val nextStates = statesAfterExtendedPurityDeletion ++ purificationStates
      nextStates.flatMap {
        case l @ Left(_)  => Iterator(l)
        case Right(value) => saturateByPurification(value)
      }
    }
  }

  def addFactors(state: State): Either[State, State] = {
    applyDerivationSteps(state, state.activeClauses.flatMap(factoringInferences))
  }

  def eliminateRedundancies(state: State): Either[State, State] = {
    redundancyStep(state) match
      case None       => Right(state)
      case Some(step) => applyDerivationSteps(state, Seq(step)).flatMap(eliminateRedundancies)
  }

  def redundancyStep(state: State): Option[DerivationStep] = {
    // check for tautologies
    val tautologyDeletion: Option[DerivationStep.TautologyDeletion] = state.activeClauses.find(_.isTaut).map(DerivationStep.TautologyDeletion(_))

    // check for eliminable constraints
    val constraintElimination: Option[DerivationStep.ConstraintElimination] =
      (for
        clause <- state.activeClauses
        case (Eq(left, right), index) <- clause.antecedent.zipWithIndex
        subst <- syntacticMGU(left, right, freeHOVariables(left) ++ freeHOVariables(right)).map(_.asFOLSubstitution)
      yield (clause, Ant(index), subst)).map[DerivationStep.ConstraintElimination](DerivationStep.ConstraintElimination(_, _, _)).headOption

    // check for subsumption
    val subsumption: Option[DerivationStep.SubsumptionDeletion] = state.activeClauses.toSeq.combinations(2).flatMap {
      case Seq(left, right) => {
        val leftSubsumptions: Seq[DerivationStep.SubsumptionDeletion] = subsumptionSubstitution(left, right).toSeq.map(s => DerivationStep.SubsumptionDeletion(left, right, s))
        val rightSubsumptions: Seq[DerivationStep.SubsumptionDeletion] = subsumptionSubstitution(right, left).toSeq.map(s => DerivationStep.SubsumptionDeletion(right, left, s))
        leftSubsumptions ++ rightSubsumptions
      }
    }.nextOption()
    tautologyDeletion.orElse(constraintElimination).orElse(subsumption)
  }

  def extendedPurityDeletionStep(state: State): Option[DerivationStep] = {
    state.variablesToEliminate.toSeq.flatMap[DerivationStep.ExtendendPurityDeletion] { w =>
      val variableOccurringClauses = state.activeClauses.filter { clause =>
        clause.exists {
          case Atom(v: Var, _) if v == w => true
          case _                         => false
        }
      }
      if variableOccurringClauses.isEmpty then None
      else
        val allCandidateOccuringClausesContainCandidatePositively = variableOccurringClauses.forall { clause =>
          clause.succedent.exists {
            case Atom(v: Var, _) if w == v => true
            case _                         => false
          }
        }
        val allCandidateOccuringClausesContainCandidateNegatively = variableOccurringClauses.forall { clause =>
          clause.antecedent.exists {
            case Atom(v: Var, _) if w == v => true
            case _                         => false
          }
        }

        val p =
          if allCandidateOccuringClausesContainCandidatePositively then Some(Polarity(true))
          else if allCandidateOccuringClausesContainCandidateNegatively then Some(Polarity(false))
          else None
        p.map(DerivationStep.ExtendendPurityDeletion(w, _))
    }.headOption
  }

  def applyDerivationSteps(state: State, derivationSteps: Iterable[DerivationStep]): Either[State, State] = {
    derivationSteps.foldLeft[Either[State, State]](Right(state)) {
      case (Left(state), _) => Left[State, State](state)
      case (Right(state), derivationStep) => {
        if state.derivationLimit.isDefined && state.derivationLimit.get <= 0 then Left(state)
        else {
          // do not count redundancy elimination to the derivation limit
          val updatedLimit = state.derivationLimit.map { limit =>
            derivationStep match
              case _: (DerivationStep.ConstraintResolution
                    | DerivationStep.ConstraintFactoring
                    | DerivationStep.PurifiedClauseDeletion
                    | DerivationStep.ExtendendPurityDeletion) => limit - 1
              case _ => limit
          }
          Right(state.copy(
            activeClauses = derivationStep(state.activeClauses),
            derivation = state.derivation.copy(inferences = state.derivation.inferences :+ derivationStep),
            derivationLimit = updatedLimit
          ))
        }
      }
    }
  }

  def purifyPointedClause(state: State, pointedClause: PointedClause): Either[State, State] = {
    val resolutionInferences = nonRedundantResolutionInferences(state.activeClauses, pointedClause)
    if resolutionInferences.isEmpty then Right(state)
    else
      for
        stateAfterResolvents <- applyDerivationSteps(state, resolutionInferences)
        stateAfterFactors <- addFactors(stateAfterResolvents)
        stateAfterRedundancyElimination <- eliminateRedundancies(stateAfterFactors)
        result <- purifyPointedClause(stateAfterRedundancyElimination, pointedClause)
      yield result
  }

  def freeFOLVariables(expr: Expr): Set[FOLVar] =
    (freeVariables(expr) -- freeHOVariables(expr)).map { case v: FOLVar => v }

  def eliminateConstraints(clause: HOLClause, keepVariables: Set[FOLVar]): HOLClause = {
    val constraint = clause.antecedent.zipWithIndex.flatMap {
      case (Eq(v @ FOLVar(_), t), i) if !keepVariables.contains(v) => Some((v, t, i))
      case (Eq(t, v @ FOLVar(_)), i) if !keepVariables.contains(v) => Some((v, t, i))
      case _                                                       => None
    }.headOption
    constraint match
      case None => clause
      case Some((v, t, i)) =>
        eliminateConstraints(Substitution(v, t)(clause.delete(Ant(i))).map { case a: Atom => a }, keepVariables)
  }

  def constraintResolvent(left: PointedClause, right: PointedClause): HOLClause = {
    val renaming = rename(freeFOLVariables(right.clause.toFormula), freeFOLVariables(left.clause.toFormula))
    val rightClausesRenamed = Substitution(renaming)(right.clause).map { case a: Atom => a }
    val rightRenamed = PointedClause(rightClausesRenamed, right.index)
    val constraints = HOLClause(left.args.zip(rightRenamed.args).map(Eq(_, _)), Seq.empty)
    val resolvent = constraints ++ left.clause.delete(left.index) ++ rightRenamed.clause.delete(rightRenamed.index)
    resolvent.distinct
  }
}
