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

  /**
    * Runs the SCAN algorithm on the input predicate elimination problem in clause form. 
    * If successful, returns a derivation whose conclusion 
    * does not contain any of the variables from the input predicate elimination problem.
    *
    * @param input predicate elimination problem in clause form
    * @param oneSidedOnly controls whether during the purification processes of SCAN only one-sided pointed clauses should be purified, i.e. pointed clauses P where the designated literal of P only occurs with a single polarity in P.
    * @param allowResolutionOnBaseLiterals controls whether resolution on base literals is allowed. Base literals are those literals whose predicate symbol is not in the variables of the input predicate elimination problem
    * @param derivationLimit controls the maximum number of inferences that 
    * derivations should have and makes sure that only derivations are returned that satisfy this limit. 
    * A value of None means that no limit is enforced, but note that this might cause non-termination.
    * @param attemptLimit controls the maximum number of SCAN runs that are to be performed to find an eliminating derivation. If None is passed no limit is enforced, but note that this might cause non-termination.
    * @return If an eliminating deirvation D is found within the given attemptLimit whose size is within derivationLimit and which respects the options oneSidedOnly and allowResolutionOnBaseLiterals, then the result is Right(D).
    * Otherwise Left(I) is returned where I is an iterator over the found derivations that do not the derivationLimit.
    */
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

  /**
    * Runs the SCAN algorithm on the input predicate elimination problem in clause form and collects different possible derivations in an iterator. 
    *
    * @param input predicate elimination problem in clause form
    * @param oneSidedOnly controls whether during the purification processes of SCAN only one-sided pointed clause should be purified, i.e. a pointed clause P where the designated literal of P only occurs with a single polarity in P.
    * @param allowResolutionOnBaseLiterals controls whether resolution on base literals is allowed. Base literals are those literals whose predicate symbol is not in the variables to be eliminated in the predicate elimination problem
    * @param derivationLimit controls the maximum number of inferences that 
    * derivations should have and makes sure that only derivations are returned that satisfy this limit. 
    * A value of None means that no limit is enforced, but note that this might cause non-termination.
    * @return Returns an iterator of derivations found during backtracked runs of SCAN. Finding these multiple derivations is done by backtracking on the different choices of purified pointed clause during the purification process of SCAN.
    * If a found derivation does not satisfy derivation limit, it is returned as Left, otherwise it is returned as Right.
    */
  def derivationsFrom(
      input: ClauseSetPredicateEliminationProblem,
      oneSidedOnly: Boolean = true,
      allowResolutionOnBaseLiterals: Boolean = false,
      derivationLimit: Option[Int] = Some(100)
  ): Iterator[Either[Derivation, Derivation]] = {
    assert(derivationLimit.isEmpty || derivationLimit.get >= 0, "derivation limit must be non-negative")
    val states = saturateByPurification(State.initialFrom(
      input,
      remainingAllowedInferences = derivationLimit,
      oneSidedOnly = oneSidedOnly,
      allowResolutionOnBaseLiterals = allowResolutionOnBaseLiterals
    ))
    states.map(state => state.map(_.derivation).left.map(_.derivation))
  }

  /**
    * A pointed clause (in analogy to pointed sets in mathematics) is a clause together with a choice of one of its literals, called the designated literal.
    *
    * @param clause the underlying clause
    * @param index the index of the literal within the clause
    */
  case class PointedClause(clause: HOLClause, index: SequentIndex):
    /**
      * Returns the designated literal of the pointed clause
      */
    def designatedLiteral = clause(index)

    /**
      * Returns rguments to the designated literal
      */
    def args = designatedLiteral match
      case Atom(_, args) => args

    /**
      * Returns the symbol underlying the designated literal of this pointed clause
      */
    def symbol: VarOrConst = designatedLiteral match
      case Atom(v @ VarOrConst(_, _, _), _) => v

    /**
      * Returns true, if the symbol of the pointed clause is a [[gapt.expr.Var]] and false otherwise
      */
    def isVar: Boolean = symbol match {
      case Var(_, _) => true
      case _         => false
    }

  /**
    * One step of a SCAN derivation
    */
  enum DerivationStep:
    /**
      * Constraint resolution step. Pointed clauses are used to indicate not only the clause on which resolution is performed, but also the specific literal.
      *
      * @param left left resolution premise
      * @param right right resolution premise
      */
    case ConstraintResolution(left: PointedClause, right: PointedClause)

    /**
      * Constraint factoring step.
      *
      * @param clause Clause to perform factoring on
      * @param principalIndex index of the literal to remain after the factoring step
      * @param auxiliaryIndex index of the literal to be removed after the factoring step
      */
    case ConstraintFactoring(clause: HOLClause, principalIndex: SequentIndex, rightIndex: SequentIndex)

    /**
      * Purified clause deletion step.
      *
      * @param pointedClause pointed clause to be deleted
      */
    case PurifiedClauseDeletion(pointedClause: PointedClause)

    /**
      * Extended purity deletion step.
      *
      * @param variable the variable on which extended purity deletion can be applied
      * @param polarity the polarity with which extended purity deletion is applied
      */
    case ExtendendPurityDeletion(variable: Var, polarity: gapt.logic.Polarity)

    /**
      * Tautology deletion step.
      *
      * @param tautology the clause that is a tautology
      */
    case TautologyDeletion(tautology: HOLClause)

    /**
      * Subsumption deletion step.
      *
      * @param subsumer the clause that subsumes subsumee
      * @param subsumee the clause that is subsumed by subsumer
      * @param substitution the substitution that shows that subsumer subsumes subsumee
      */
    case SubsumptionDeletion(subsumer: HOLClause, subsumee: HOLClause, substitution: FOLSubstitution)

    /**
      * Constraint elimination step.
      *
      * @param clause the clause to apply constraint elimination to
      * @param constraintIndex the index of the constraint to be eliminated
      * @param substitution the substitution unifying the arguments in the constraint
      */
    case ConstraintElimination(clause: HOLClause, constraintIndex: SequentIndex, substitution: FOLSubstitution)

    private def addedRemovedClauses(clauses: Set[HOLClause]): (Set[HOLClause], Set[HOLClause]) =
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

    /**
      * Applies the derivation step to a given clause set returning the resulting conclusion
      *
      * @param clauses the premise of the derivation step
      * @return the clause set resulting from applying the derivation step to the premise
      */
    def apply(clauses: Set[HOLClause]): Set[HOLClause] =
      val (added, removed) = addedRemovedClauses(clauses)
      (clauses ++ added) -- removed

  /**
    * A SCAN derivation
    *
    * @param from the initial predicate elimination problem from which we start
    * @param derivationSteps the derivation steps performed
    */
  case class Derivation(
      from: ClauseSetPredicateEliminationProblem,
      derivationSteps: List[DerivationStep]
  ):
    /**
      * @return The derivation resulting from this by applying the first derivation step to the input predicate elimination problem and keeping the remaining derivation steps.
      * Returns [[UnsupportedOperationException]] if there are no derivation steps
      */
    def tail: Derivation = derivationSteps match
      case head :: next => Derivation(
          ClauseSetPredicateEliminationProblem(
            from.varsToEliminate,
            head(from.firstOrderClauses)
          ),
          next
        )
      case Nil => throw UnsupportedOperationException("tail of empty derivation")

    /**
      * @return conclusion, i.e. the last clause set, of the derivation
      */
    def conclusion: Set[HOLClause] = derivationSteps match
      case Nil => from.firstOrderClauses
      case head :: next => Derivation(
          ClauseSetPredicateEliminationProblem(
            from.varsToEliminate,
            head(from.firstOrderClauses)
          ),
          next
        ).conclusion

  object Derivation:
    /**
      * @param from predicate elimination problem to start from
      * @return a derivation without derivation steps, starting from an initial predicate elimination problem
      */
    def emptyFrom(from: ClauseSetPredicateEliminationProblem): Derivation =
      Derivation(from, List.empty)

  /**
    * Describes the state of the SCAN saturation process at any given time
    *
    * @constructor
    * @param activeClauses the active clause set
    * @param derivation the current derivation we are at
    * @param remainingAllowedInferences the remaining number of inference steps. If None, an arbitrary amount of inferences is allowed
    * @param oneSidedOnly @see oneSidedOnly option of scan
    * @param allowResolutionOnBaseLiterals @see allowResolutionOnBaseLiterals option of scsan
    */
  case class State(
      activeClauses: Set[HOLClause],
      derivation: Derivation,
      remainingAllowedInferences: Option[Int],
      oneSidedOnly: Boolean,
      allowResolutionOnBaseLiterals: Boolean
  ):
    def variablesToEliminate = derivation.from.varsToEliminate
    def isEliminated = activeClauses.forall(c => freeHOVariables(c.toFormula).intersect(variablesToEliminate.toSet).isEmpty)
    def isPointedClauseWithEliminationVariable(pointedClause: PointedClause) =
      pointedClause.isVar && variablesToEliminate.contains(pointedClause.symbol.asInstanceOf[Var])

  object State:
    /**
      * Returns an initial state given a predicate elimination problem and global parameters for the saturation process
      *
      * @param input the predicate elimination problem form which to start
      * @param remainingAllowedInferences @see remainingAllowedInferences field of State
      * @param oneSidedOnly @see oneSidedOnly option of scan
      * @param allowResolutionOnBaseLiterals @see allowResolutionOnBaseLiterals option of
      * @return
      */
    def initialFrom(
        input: ClauseSetPredicateEliminationProblem,
        remainingAllowedInferences: Option[Int],
        oneSidedOnly: Boolean,
        allowResolutionOnBaseLiterals: Boolean
    ): State = State(
      input.firstOrderClauses,
      Derivation.emptyFrom(input),
      remainingAllowedInferences,
      oneSidedOnly,
      allowResolutionOnBaseLiterals
    )

  /**
    * Applies the SCAN purification process to a given state with a given pointed clause which need not necessarily be part of the active clauses the given state
    *
    * @param state state at which to perform purification
    * @param pointedClause pointed clause with respect to which to perform purification
    * @return if the purification process could be completed within the limits given in state, returns Right with the new state, otherwise returns Left with a state where the limit was reached
    */
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
      val hoVar @ Var(_, _) = rc.symbol: @unchecked
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

    val (oneSidedPurifications, mixedPurifications) = purifications.partition(i => isOneSided(i.pointedClause))

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
      case Atom(v: VarOrConst, _) => v != pointedClause.symbol
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
      rc => rc.symbol == resolutionCandidate.symbol && rc.index.polarity == !resolutionCandidate.index.polarity
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
        if state.remainingAllowedInferences.isDefined && state.remainingAllowedInferences.get <= 0 then Left(state)
        else {
          // do not count redundancy elimination to the derivation limit
          val updatedLimit = state.remainingAllowedInferences.map { limit =>
            derivationStep match
              case _: (DerivationStep.ConstraintResolution
                    | DerivationStep.ConstraintFactoring
                    | DerivationStep.PurifiedClauseDeletion
                    | DerivationStep.ExtendendPurityDeletion) => limit - 1
              case _ => limit
          }
          Right(state.copy(
            activeClauses = derivationStep(state.activeClauses),
            derivation = state.derivation.copy(derivationSteps = state.derivation.derivationSteps :+ derivationStep),
            remainingAllowedInferences = updatedLimit
          ))
        }
      }
    }
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
