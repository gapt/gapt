package gapt.logic.hol

import gapt.expr.*
import gapt.proofs.{Ant, HOLClause, RichFormulaSequent, Sequent, SequentIndex, Suc}
import gapt.expr.util.rename
import gapt.expr.util.freeVariables
import gapt.expr.subst.Substitution
import gapt.expr.formula.{Atom, Eq}
import gapt.expr.formula.hol.freeHOVariables
import gapt.expr.formula.fol.FOLVar
import gapt.expr.util.syntacticMGU
import gapt.expr.subst.FOLSubstitution
import gapt.logic.Polarity
import gapt.logic.clauseSubsumption
import gapt.utils.{Logger}

import gapt.expr.formula.constants.EqC
import gapt.expr.formula.fol.FOLTerm
import scala.annotation.tailrec

object scan {

  val logger = Logger("scan")

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
    * @return If an eliminating deirvation D is found within the given attemptLimit whose size is within derivationLimit and which respects the options oneSidedOnly and allowResolutionOnBaseLiterals, then the result is Some(D). Returns None otherwise
    * Otherwise Left(I) is returned where I is an iterator over the found derivations that do not the derivationLimit.
    */
  def apply(
      input: ClauseSetPredicateEliminationProblem,
      oneSidedOnly: Boolean = true,
      allowResolutionOnBaseLiterals: Boolean = false,
      derivationLimit: Option[Int] = Some(100),
      attemptLimit: Option[Int] = Some(10)
  ): Option[Derivation] = {
    val baseIterator = scan.derivationsFrom(
      input = input,
      oneSidedOnly = oneSidedOnly,
      allowResolutionOnBaseLiterals = allowResolutionOnBaseLiterals,
      derivationLimit = derivationLimit
    )
    val iterator = attemptLimit.map(l => baseIterator.take(l)).getOrElse(baseIterator)

    iterator
      .collect { case Right(value) => value }
      .nextOption()
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
    logger.info(s"input clause set: ${input.firstOrderClauses}")
    val states = runScan(
      State.initialFrom(
        input,
        remainingAllowedInferences = derivationLimit,
        oneSidedOnly = oneSidedOnly,
        allowResolutionOnBaseLiterals = allowResolutionOnBaseLiterals
      )
    )
    states.map(state => state.map(_.derivation).left.map(_.derivation))
  }

  /**
    * A pointed clause (in analogy to pointed sets in mathematics) is a clause together with a choice of one of its literals, called the designated literal.
    *
    * @param clause the underlying clause
    * @param index the index of the literal within the clause
    */
  case class PointedClause(clause: HOLClause, index: SequentIndex) {

    /**
      * Returns the designated literal of the pointed clause
      */
    def designatedLiteral = clause(index)

    def polarity = index.polarity

    /**
      * Returns arguments to the designated literal
      */
    def args: List[Expr] = designatedLiteral match
      case Atom(_, args) => args

    /**
      * Returns the symbol underlying the designated literal of this pointed clause
      */
    def symbol: VarOrConst = designatedLiteral match
      case Atom(v @ VarOrConst(_, _, _), _) => v

    /**
      * Returns Some(v), if the symbol of the pointed clause is a [[gapt.expr.Var]] and None otherwise
      */
    def varOption: Option[Var] = symbol match
      case v: Var => Some(v)
      case _      => None

    def isOneSided: Boolean = {
      clause.cedent(!index.polarity).forall {
        case Atom(v: VarOrConst, _) => v != symbol
        case _                      => true
      }
    }
  }

  object PointedClause {
    def apply(clause: HOLClause, index: SequentIndex): PointedClause = {
      assert(clause.indices.contains(index), s"clause $clause does not have index $index")
      new PointedClause(clause, index)
    }
  }

  /**
    * One step of a SCAN derivation
    */
  enum DerivationStep {

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
    case VariableElimination(clause: HOLClause, constraintIndex: SequentIndex, substitution: FOLSubstitution)

    def addedRemovedClauses(clauses: Set[HOLClause]): (Set[HOLClause], Set[HOLClause]) =
      this match
        case ConstraintResolution(left, right)                     => (Set(constraintResolvent(left, right)), Set.empty)
        case f: ConstraintFactoring                                => (Set(factor(f)), Set.empty)
        case PurifiedClauseDeletion(candidate)                     => (Set.empty, Set(candidate.clause))
        case SubsumptionDeletion(subsumer, subsumee, substitution) => (Set.empty, Set(subsumee))
        case TautologyDeletion(clause)                             => (Set.empty, Set(clause))
        case VariableElimination(clause, index, substitution)      => (Set(substitution(clause.delete(index)).map { case a: Atom => a }.distinct), Set(clause))
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
  }

  /**
    * A SCAN derivation
    *
    * @param from the initial predicate elimination problem from which we start
    * @param derivationSteps the derivation steps performed
    */
  case class Derivation(
      from: ClauseSetPredicateEliminationProblem,
      derivationSteps: List[DerivationStep]
  ) {

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
  }

  object Derivation {

    /**
      * @param from predicate elimination problem to start from
      * @return a derivation without derivation steps, starting from an initial predicate elimination problem
      */
    def emptyFrom(from: ClauseSetPredicateEliminationProblem): Derivation =
      Derivation(from, List.empty)
  }

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
  ) {
    def variablesToEliminate = derivation.from.varsToEliminate
    def isEliminated = activeClauses.forall(c => freeHOVariables(c.toFormula).intersect(variablesToEliminate.toSet).isEmpty)
    def isPointedClauseWithEliminationVariable(pointedClause: PointedClause) =
      pointedClause.varOption.map(variablesToEliminate.contains).getOrElse(false)
    def isFirstOrder(expr: Expr): Boolean = freeHOVariables(expr).intersect(variablesToEliminate.toSet).isEmpty
  }

  object State {

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
  }

  import scala.collection.mutable.Stack
  private case class StateIterator(val stack: Stack[Either[State, State]]) extends Iterator[Either[State, State]] {
    def hasNext: Boolean = !stack.isEmpty
    @tailrec final def next(): Either[State, State] = {
      if stack.isEmpty then
        throw new NoSuchElementException("no more states")

      val s = stack.pop()
      val state = s match {
        case Left(s)      => return Left(s)
        case Right(state) => state
      }

      if state.isEliminated then
        return Right(state)

      val stateAfterExtendedPurityDeletion = extendedPurityDeletionStep(state) match {
        case None => state
        case Some(step) => applyDerivationSteps(state, Seq(step)) match {
            case Left(s) => return Left(s)
            case Right(s) => {
              // push this state and return next to perform further extended
              // purity deletion steps
              stack.push(Right(s))
              return next()
            }
          }
      }

      val stateAfterFactors =
        for
          redElimination <- eliminateRedundancies(stateAfterExtendedPurityDeletion)
          factoring <- addFactors(redElimination)
          redElimination <- eliminateRedundancies(factoring)
        yield redElimination

      val stateAfterRedundancyEliminatedFactors = stateAfterFactors match {
        case Left(s)  => return Left(s)
        case Right(s) => s
      }

      if stateAfterRedundancyEliminatedFactors.isEliminated then
        return Right(stateAfterRedundancyEliminatedFactors)

      val candidatePointedClauses = purificationCandidates(stateAfterRedundancyEliminatedFactors).toSeq
      val statesAfterPurification = candidatePointedClauses
        .map(purifyPointedClause(stateAfterRedundancyEliminatedFactors, _))

      stack.addAll(statesAfterPurification)
      next()
    }
  }

  def runScan(state: State): Iterator[Either[State, State]] = {
    return StateIterator(Stack(Right(state)))
  }

  def nonRedundantResolutionInferences(
      pointedClause: PointedClause,
      clauseSet: Set[HOLClause]
  ): Iterator[DerivationStep.ConstraintResolution] = {
    def forwardSubsumes(clause: HOLClause, resolvent: HOLClause): Boolean = {
      isInjectivelySubsumedAfterVariableElimination(
        pointedClause.symbol,
        !pointedClause.index.polarity,
        clause,
        resolvent
      )
    }

    resolutionInferences(clauseSet, pointedClause).iterator.filter {
      case DerivationStep.ConstraintResolution(left, right) =>
        val resolvent = constraintResolvent(left, right)
        clauseSet.forall(c => !forwardSubsumes(c, resolvent))
    }
  }

  def purificationCandidates(state: State): Iterator[PointedClause] = {
    val purifiablePointedClauses = pointedClauses(state.activeClauses)
      .filter(state.isPointedClauseWithEliminationVariable)

    // order pointed clauses where already purified clauses are preferred
    // over ones that need purification and then one-sided ones are preferred
    // over mixed ones
    val orderedPurifiablePointedClauses = purifiablePointedClauses.toSeq.sortBy {
      case p => (isPurified(p, state.activeClauses - p.clause), p.isOneSided) match {
          case (true, true)   => 0
          case (true, false)  => 1
          case (false, true)  => 2
          case (false, false) => 3
        }
    }

    val (oneSidedCandidates, mixedCandidates) = orderedPurifiablePointedClauses.partition(_.isOneSided)
    if state.oneSidedOnly && oneSidedCandidates.isEmpty then {
      logger.warn(s"no one-sided purification candidates available, but only allowed to use one-sided resolution")
      Iterator.empty
    } else {
      val candidates = if state.oneSidedOnly then oneSidedCandidates else orderedPurifiablePointedClauses
      candidates.iterator
    }
  }

  /**
    * Applies the SCAN purification process to a given state with a given pointed clause which need not necessarily be part of the active clauses the given state
    *
    * @param state state at which to perform purification
    * @param pointedClause pointed clause with respect to which to perform purification
    * @return if the purification process could be completed within the limits given in state, returns Right with the new state, otherwise returns Left with a state where the limit was reached
    */
  def purifyPointedClause(state: State, pointedClause: PointedClause): Either[State, State] = {
    val resolutionInferences = nonRedundantResolutionInferences(pointedClause, state.activeClauses - pointedClause.clause)
    if resolutionInferences.isEmpty then
      if state.isPointedClauseWithEliminationVariable(pointedClause) then
        applyDerivationSteps(state, Seq(DerivationStep.PurifiedClauseDeletion(pointedClause)))
      else
        Right(state) // do not delete pointed clause if resolution is performed on base symbols
    else
      for
        stateWithResolvents <- applyDerivationSteps(state, resolutionInferences)
        stateAfterVariableElimination <- eliminateVariableConstraints(stateWithResolvents)
        purifiedState <- purifyPointedClause(stateAfterVariableElimination, pointedClause)
      yield purifiedState
  }

  def factor(factoring: DerivationStep.ConstraintFactoring): HOLClause = {
    val DerivationStep.ConstraintFactoring(clause, leftIndex, rightIndex) = factoring
    val Atom(_, leftArgs) = clause(leftIndex): @unchecked
    val Atom(_, rightArgs) = clause(rightIndex): @unchecked
    val constraints = leftArgs.zip(rightArgs).map(Eq(_, _))
    (clause.delete(rightIndex) ++ HOLClause(constraints, Seq.empty)).distinct
  }

  def isFactorOf(state: State, clause: HOLClause, other: HOLClause): Boolean = {
    factoringInferences(state, other).exists(i => factor(i) == clause)
  }

  def factoringInferences(state: State, clause: HOLClause): Set[DerivationStep.ConstraintFactoring] = {
    val succeedentInferences = clause.succedent.zipWithIndex.combinations(2).flatMap {
      case Seq(left @ (Atom(leftHead, _), _: Int), right @ (Atom(rightHead, _), _: Int))
          if leftHead == rightHead && state.variablesToEliminate.contains(leftHead) => Some((left, right))
      case _ => None
    }.map[DerivationStep.ConstraintFactoring] {
      case ((_, leftIndex), (_, rightIndex)) => DerivationStep.ConstraintFactoring(clause, Suc(leftIndex), Suc(rightIndex))
    }.toSet
    val antecedentInferences =
      clause.antecedent.zipWithIndex.combinations(2).flatMap {
        case Seq(left @ (Atom(leftHead, _), _: Int), right @ (Atom(rightHead, _), _: Int))
            if leftHead == rightHead && state.variablesToEliminate.contains(leftHead) => Some((left, right))
        case _ => None
      }.map[DerivationStep.ConstraintFactoring] {
        case ((_, leftIndex), (_, rightIndex)) => DerivationStep.ConstraintFactoring(clause, Ant(leftIndex), Ant(rightIndex))
      }.toSet

    succeedentInferences ++ antecedentInferences
  }

  def subsumptionSubstitution(subsumer: HOLClause, subsumee: HOLClause): Option[FOLSubstitution] = {
    val subsumerHoVarsAsConsts = subsumer.map { case Atom(VarOrConst(v, ty, tys), args) => Atom(Const(v, ty, tys), args) }
    val subsumeeHoVarsAsConsts = subsumee.map { case Atom(VarOrConst(v, ty, tys), args) => Atom(Const(v, ty, tys), args) }
    clauseSubsumption(subsumerHoVarsAsConsts, subsumeeHoVarsAsConsts, multisetSubsumption = true).map(_.asFOLSubstitution)
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

  def addFactors(state: State): Either[State, State] = {
    applyDerivationSteps(state, state.activeClauses.flatMap(factoringInferences(state, _)))
  }

  def eliminateRedundancies(state: State): Either[State, State] = {
    redundancyStep(state) match
      case None       => Right(state)
      case Some(step) => applyDerivationSteps(state, Seq(step)).flatMap(eliminateRedundancies)
  }

  def eliminateVariableConstraints(state: State): Either[State, State] = {
    variableEliminationStep(state) match
      case None       => Right(state)
      case Some(step) => applyDerivationSteps(state, Seq(step)).flatMap(eliminateVariableConstraints)
  }

  def variableEliminationStep(state: State): Option[DerivationStep.VariableElimination] = {
    state.activeClauses.flatMap { clause => oneStepVariableEliminationSteps(clause) }.headOption
  }

  def redundancyStep(state: State): Option[DerivationStep] = {
    // check for tautologies
    val tautologyDeletion: Option[DerivationStep.TautologyDeletion] = state.activeClauses.find(_.isTaut).map(DerivationStep.TautologyDeletion(_))

    // check for eliminable constraints
    val variableElimination: Option[DerivationStep.VariableElimination] = variableEliminationStep(state)

    // check for subsumption
    val subsumption: Option[DerivationStep.SubsumptionDeletion] = state.activeClauses.toSeq.combinations(2).flatMap {
      case Seq(left, right) => {
        val leftSubsumptions: Seq[DerivationStep.SubsumptionDeletion] = subsumptionSubstitution(left, right).toSeq.map(s => DerivationStep.SubsumptionDeletion(left, right, s))
        val rightSubsumptions: Seq[DerivationStep.SubsumptionDeletion] = subsumptionSubstitution(right, left).toSeq.map(s => DerivationStep.SubsumptionDeletion(right, left, s))
        leftSubsumptions ++ rightSubsumptions
      }
    }.nextOption()
    tautologyDeletion.orElse(variableElimination).orElse(subsumption)
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

  def applyDerivationSteps(state: State, derivationSteps: Iterator[DerivationStep]): Either[State, State] = {
    derivationSteps.foldLeft[Either[State, State]](Right(state)) {
      case (Left(state), _) => Left[State, State](state)
      case (Right(state), derivationStep) => {
        if state.remainingAllowedInferences.isDefined && state.remainingAllowedInferences.get <= 0 then {
          logger.info("limit of allowed inferences reached")
          Left(state)
        } else {
          logger.info(s"applying $derivationStep")
          // do not count redundancy elimination to the derivation limit
          val updatedLimit = state.remainingAllowedInferences.map { limit =>
            derivationStep match
              case _: (DerivationStep.ConstraintResolution
                    | DerivationStep.ConstraintFactoring
                    | DerivationStep.PurifiedClauseDeletion
                    | DerivationStep.ExtendendPurityDeletion) => limit - 1
              case _ => limit
          }
          val updatedActiveClauses = derivationStep(state.activeClauses)
          val updatedState = state.copy(
            activeClauses = updatedActiveClauses,
            derivation = state.derivation.copy(derivationSteps = state.derivation.derivationSteps :+ derivationStep),
            remainingAllowedInferences = updatedLimit
          )
          logger.info(s"active clause set: ${updatedState.activeClauses}")
          Right(updatedState)
        }
      }
    }
  }

  def applyDerivationSteps(
      state: State,
      derivationSteps: Iterable[DerivationStep]
  ): Either[State, State] = {
    applyDerivationSteps(state, derivationSteps.iterator)
  }

  def freeFOLVariables(expr: Expr): Set[FOLVar] =
    (freeVariables(expr) -- freeHOVariables(expr)).map { case v: FOLVar => v }

  def constraintResolvent(left: PointedClause, right: PointedClause): HOLClause = {
    val renaming = rename(freeFOLVariables(right.clause.toFormula), freeFOLVariables(left.clause.toFormula))
    val rightClausesRenamed = Substitution(renaming)(right.clause).map { case a: Atom => a }
    val rightRenamed = PointedClause(rightClausesRenamed, right.index)
    val constraints = HOLClause(left.args.zip(rightRenamed.args).map(Eq(_, _)), Seq.empty)
    val resolvent = constraints ++ left.clause.delete(left.index) ++ rightRenamed.clause.delete(rightRenamed.index)
    resolvent.distinct
  }

  def isPurified(pointedClause: PointedClause, clauseSet: Set[HOLClause]): Boolean = {
    nonRedundantResolutionInferences(pointedClause, clauseSet).isEmpty
  }

  def isInjectivelySubsumedAfterVariableElimination(
      symbol: VarOrConst,
      polarity: Polarity,
      left: HOLClause,
      right: HOLClause
  ): Boolean =
    variableEliminations(right).exists(c => isLSubsumed(symbol, polarity, left, c))

  def oneStepVariableEliminationSteps(clause: HOLClause): Set[DerivationStep.VariableElimination] = {
    val variableConstraints = clause.antecedent.zipWithIndex.collect {
      case (Eq(v: FOLVar, t: FOLTerm), i) if !isProperSubterm(v, t) => (i, v, t)
      case (Eq(t: FOLTerm, v: FOLVar), i) if !isProperSubterm(v, t) => (i, v, t)
    }

    variableConstraints.map[DerivationStep.VariableElimination] { (i, v, t) =>
      DerivationStep.VariableElimination(clause, Ant(i), FOLSubstitution(v, t))
    }.toSet
  }

  def oneStepVariableEliminations(clause: HOLClause): Set[HOLClause] = {
    oneStepVariableEliminationSteps(clause).flatMap(i => i(Set(clause)))
  }

  def variableEliminations(clause: HOLClause): Set[HOLClause] =
    val oneStepEliminations = oneStepVariableEliminations(clause)
    Set(clause) ++ oneStepEliminations.flatMap(e => variableEliminations(e))

  def isProperSubterm(left: FOLTerm, right: FOLTerm): Boolean =
    left != right && right.contains(left)

  def injectiveSubsumptions(
      symbol: VarOrConst,
      polarity: Polarity,
      left: HOLClause,
      right: HOLClause
  ): Seq[Substitution] = {
    def argsWithSymbolAndPolarity(clause: HOLClause): Seq[(SequentIndex, List[FOLTerm])] = {
      clause.zipWithIndex.cedent(polarity).collect {
        case (Atom(head, args), i) if head == symbol => (i, args.asInstanceOf[List[FOLTerm]])
      }
    }

    val leftArgsWithSymbolAndPolarity = argsWithSymbolAndPolarity(left)
    val rightArgsWithSymbolAndPolarity = argsWithSymbolAndPolarity(right)
    val leftSize = leftArgsWithSymbolAndPolarity.size
    val rightSize = rightArgsWithSymbolAndPolarity.size
    if leftSize > rightSize then
      return Seq.empty

    val blacklist = containedNames(left) ++ containedNames(right) + symbol
    val nameGenerator = rename.awayFrom(blacklist)
    val freshPredicateSymbols = nameGenerator
      .freshStream(symbol.name)
      .map(v => Var(v, symbol.ty))
      .take(rightSize)
      .toVector

    def clauseWithFreshSymbols(clause: HOLClause, f: Map[Int, Int]) = {
      val indexWithArgs = argsWithSymbolAndPolarity(clause)
      clause.delete(indexWithArgs.map(_._1)) ++
        Sequent(indexWithArgs.zipWithIndex.map {
          case ((seqIndex, args), i) => {
            (Atom(freshPredicateSymbols(f(i)), args), seqIndex.polarity)
          }
        })
    }

    val idPairs = (0 to (rightSize - 1)).map(i => (i, i))
    val rightWithFreshSymbols = clauseWithFreshSymbols(right, Map(idPairs*))

    injectiveMappings(leftSize, rightSize).flatMap(f => {
      val leftWithFreshSymbols = clauseWithFreshSymbols(left, f)
      val hoVars = freeHOVariables(leftWithFreshSymbols.toFormula) ++
        freeHOVariables(rightWithFreshSymbols.toFormula)
      val hoVarsAsConsts = hoVars.map {
        case v @ Var(name, ty) => (v, Const(nameGenerator.fresh(name), ty))
      }.toMap
      val leftHoVarsAsConsts = leftWithFreshSymbols.map {
        case Atom(v: Var, args) => Atom(hoVarsAsConsts(v), args)
        case a                  => a
      }
      val rightHoVarsAsConsts = rightWithFreshSymbols.map {
        case Atom(v: Var, args) => Atom(hoVarsAsConsts(v), args)
        case a                  => a
      }
      clauseSubsumption(leftHoVarsAsConsts, rightHoVarsAsConsts).map(_.asFOLSubstitution)
    })
  }

  def isLSubsumed(symbol: VarOrConst, polarity: Polarity, left: HOLClause, right: HOLClause): Boolean = {
    injectiveSubsumptions(symbol, polarity, left, right).nonEmpty
  }

  def injectiveMappings(fromSize: Int, toSize: Int): Seq[Map[Int, Int]] =
    assert(fromSize >= 0)
    assert(toSize >= 0)
    if fromSize == 0 then return Seq(Map.empty)
    if fromSize > toSize then return Seq.empty

    val smallerMappings = injectiveMappings(fromSize - 1, toSize)
    smallerMappings.flatMap(m => {
      val choicesLeft = (0 to (toSize - 1)).toSet -- m.values.toSet
      choicesLeft.map(j => m.updated(fromSize - 1, j))
    })

  def reasonsThatDerivationStepIsIncorrect(
      step: DerivationStep,
      premise: Set[HOLClause],
      conclusion: Set[HOLClause]
  ): Seq[String] = {
    import scala.util.boundary
    import gapt.expr.ty.Ti

    def break(using scala.util.boundary.Label[Unit]) = boundary.break(())
    val reasons = scala.collection.mutable.Buffer[String]()
    def report(reason: String) = reasons += reason
    boundary {
      step match {
        case DerivationStep.ConstraintResolution(left, right) => {
          if !premise.contains(left.clause) then
            report(s"""premise does not contain left clause of resolution inference
                          |premise: $premise
                          |left: ${left.clause}""".stripMargin)
          if !premise.contains(right.clause) then
            report(s"""premise does not contain right clause of resolution inference
                          |premise: $premise
                          |right: ${right.clause}""".stripMargin)

          val arePolaritiesSame = left.polarity == right.polarity
          val areSymbolsSame = left.symbol == right.symbol
          if arePolaritiesSame then
            report(s"""polarity of left and right pointed clause are the same, but should be different
                          |left: $left
                          |right: $right""".stripMargin)
          if !areSymbolsSame then
            report(s"""symbol of left and right pointed clause are the same, but should be different
                          |left: $left
                          |right: $right""".stripMargin)

          if arePolaritiesSame || !areSymbolsSame then
            break

          val resolvent = constraintResolvent(left, right)
          val expectedConclusion = premise + resolvent
          if !conclusion.contains(resolvent) then
            report(s"""conclusion does not contain constraint resolvent
                          |conclusion: $conclusion
                          |left: $left
                          |right: $right
                          |resolvent: $resolvent""".stripMargin)

          val nonPresentPremiseClauses = premise -- conclusion
          if nonPresentPremiseClauses.nonEmpty then
            report(s"""conclusion does not contain premise clauses
                          |conclusion: $conclusion
                          |premise: $premise
                          |clauses in premise, but not in conclusion: $nonPresentPremiseClauses""")

          val unexpectedClauses = conclusion -- expectedConclusion
          if unexpectedClauses.nonEmpty then
            report(s"""conclusion contains unexpected clauses
                        |conclusion: $conclusion
                        |expected conclusion: $expectedConclusion
                        |unexpected clauses: $unexpectedClauses""".stripMargin)
        }
        case f @ DerivationStep.ConstraintFactoring(clause, principalIndex, auxiliaryIndex) => {
          if !premise.contains(clause) then
            report("""premise does not contain clause to be factored
                          |premise: $premise
                          |clause: $clause""".stripMargin)

          val containsPrincipalIndex = clause.indices.contains(principalIndex)
          if !containsPrincipalIndex then
            report(s"""clause to be factored does not contain the principal index
                          |clause: $clause
                          |principalIndex: $principalIndex""".stripMargin)

          val containsAuxiliaryIndex = clause.indices.contains(auxiliaryIndex)
          if !containsAuxiliaryIndex then
            report(s"""clause to be factored does not contain the auxiliary index
                          |clause: $clause
                          |auxiliary index: $auxiliaryIndex""".stripMargin)

          val polaritiesAreSame = principalIndex.polarity == auxiliaryIndex.polarity
          if !polaritiesAreSame then
            report(s"""polarities of the factoring literals do not match
                          |clause: $clause
                          |principal index: $principalIndex
                          |auxiliary index: $auxiliaryIndex""".stripMargin)

          if !containsPrincipalIndex || !containsAuxiliaryIndex then
            break

          val principalLiteral = clause(principalIndex)
          val auxiliaryLiteral = clause(auxiliaryIndex)
          if principalLiteral.head != auxiliaryLiteral.head then
            report(s"""literals to be factored on don't have the same head symbol
                          |principal literal: $principalLiteral
                          |auxiliary literal: $auxiliaryLiteral""".stripMargin)
            break

          val constraintFactor = factor(f)
          if !conclusion.contains(constraintFactor) then
            report(s"""conclusion does not contain constraint factor
                          |conclusion: $conclusion
                          |clause to factor: $clause
                          |factor: $constraintFactor""".stripMargin)

          val expectedConclusion = premise + constraintFactor
          val clausesInPremiseButNotConclusion = premise -- conclusion
          if clausesInPremiseButNotConclusion.nonEmpty then
            report(s"""conclusion does not contain premise clauses
                          |conclusion: $conclusion
                          |premise: $premise
                          |clauses in premise, but not in conclusion: $clausesInPremiseButNotConclusion""")

          val unexpectedClauses = conclusion -- expectedConclusion
          if unexpectedClauses.nonEmpty then
            report(s"""conclusion contains unexpected clauses
                          |expected conclusion: $expectedConclusion
                          |unexpected clauses: $unexpectedClauses""".stripMargin)
        }

        case DerivationStep.VariableElimination(clause, constraintIndex, substitution) => {
          if !premise.contains(clause) then
            report(s"""premise does not contain clause to be eliminated
                          |premise: $premise
                          |clause: $clause""".stripMargin)

          if !clause.indices.contains(constraintIndex) then
            report(s"""clause does not contain constraint index
                        |clause: $clause
                        |constraint index: $constraintIndex""".stripMargin)
            break

          if !constraintIndex.isAnt then
            report(s"""constraint is not in the antecedent
                        |constraint index: $constraintIndex""".stripMargin)

          val constraint = clause(constraintIndex)
          if constraint.head != EqC(Ti) then
            report(s"""constraint literal is not an equality literal
                      |clause: $clause
                      |constraint literal: $constraint""".stripMargin)
            break

          val (left, right) = constraint.args match {
            case List(left: FOLTerm, right: FOLTerm) => (left, right)
            case c =>
              throw new IllegalStateException(
                s"""equality has fewer than 2 or more than 2 arguments passed to it which should not occur and we do not handle
                     |got constraints: $c""".stripMargin
              )
          }

          val leftAfterSubstitution = substitution(left)
          val rightAfterSubstitution = substitution(right)
          if leftAfterSubstitution != rightAfterSubstitution then
            report(s"""substitution does not unify left and right term
                        |clause: $clause
                        |constraint: $constraint
                        |left: $left
                        |right: $right
                        |substitution: $substitution
                        |left after substitution: $leftAfterSubstitution
                        |right after substitution: $rightAfterSubstitution""".stripMargin)
            break

          val furtherMgu = syntacticMGU(leftAfterSubstitution, rightAfterSubstitution).get
          if !furtherMgu.isIdentity then
            report(s"""substitution unifies left and right, but is not a most general unifier
                        |clause: $clause
                        |constraint: $constraint
                        |left: $left
                        |right: $right
                        |substitution: $substitution
                        |left after substitution: $leftAfterSubstitution
                        |right after substitution: $rightAfterSubstitution
                        |further non-trivial unification by: $furtherMgu""".stripMargin)

          val clauseAfterConstraintElimination = substitution(clause.delete(constraintIndex)).map { case a: Atom => a }.distinct
          val nonReplacedPremise = premise - clause
          val expectedConclusion = nonReplacedPremise + clauseAfterConstraintElimination
          if !conclusion.contains(clauseAfterConstraintElimination) then
            report(s"""conclusion does not contain clause after eliminated constraint
                        |conclusion: $conclusion
                        |clause after constraint elimination: $clauseAfterConstraintElimination""".stripMargin)

          val nonReplacedClausesInPremiseButNotConclusion = nonReplacedPremise -- conclusion
          if nonReplacedClausesInPremiseButNotConclusion.nonEmpty then
            report(s"""conclusion does not contain premise clauses
                         |conclusion: $conclusion
                         |premise without clause to be removed: $nonReplacedPremise
                         |clauses in premise, but not in conclusion: $nonReplacedClausesInPremiseButNotConclusion""")

          val unexpectedClauses = conclusion -- expectedConclusion
          if unexpectedClauses.nonEmpty then
            report(s"""conclusion contains unexpected clauses
                        |conclusion: $conclusion
                        |expected conclusion: $expectedConclusion
                        |unexpected clauses: $unexpectedClauses""".stripMargin)
        }
        case DerivationStep.ExtendendPurityDeletion(variable, polarity) => {
          val clausesContainingVariable = premise.filter(c => containedNames(c).contains(variable))
          val (clausesContainingVariableWithPolarity, clausesContainingVariableNotWithPolarity) =
            clausesContainingVariable.partition(c =>
              c.cedent(polarity).exists {
                case Atom(head, _) => head == variable
                case _             => false
              }
            )

          if clausesContainingVariableNotWithPolarity.nonEmpty then
            report(s"""side condition violated: there are clauses that contain variable, but only with opposite polarity
                        |premise: $premise
                        |variable: $variable
                        |polarity: $polarity
                        |clauses containing variable with only opposite variable: $clausesContainingVariableNotWithPolarity""".stripMargin)

          val expectedConclusion = premise -- clausesContainingVariable
          val missingClauses = expectedConclusion -- conclusion
          if missingClauses.nonEmpty then
            report(s"""conclusion is missing clauses
                        |conclusion: $conclusion
                        |expected conclusion: $expectedConclusion
                        |missing clauses: $missingClauses""".stripMargin)

          val unexpectedClauses = conclusion -- expectedConclusion
          if unexpectedClauses.nonEmpty then
            report(s"""conclusion contains unexpected clauses
                        |conclusion: $conclusion
                        |expected conclusion: $expectedConclusion
                        |unexpected clauses: $unexpectedClauses""".stripMargin)
        }
        case DerivationStep.TautologyDeletion(tautology) => {
          if !premise.contains(tautology) then
            report(s"""premise does not contain tautology to be eliminated
                        |premise: $premise
                        |tautology: $tautology""".stripMargin)

          if !tautology.isTaut then
            report(s"""tautology candidate is not a tautology
                        |candidate: $tautology""".stripMargin)

          val expectedConclusion = premise - tautology

          val missingClauses = expectedConclusion -- conclusion
          if missingClauses.nonEmpty then
            report(s"""conclusion is missing clauses
                        |conclusion: $conclusion
                        |expected conclusion: $expectedConclusion
                        |missing clauses: $missingClauses""".stripMargin)

          val unexpectedClauses = conclusion -- expectedConclusion
          if unexpectedClauses.nonEmpty then
            report(s"""conclusion contains unexpected clauses
                        |conclusion: $conclusion
                        |expected conclusion: $expectedConclusion
                        |unexpected clauses: $unexpectedClauses""".stripMargin)
        }

        case DerivationStep.SubsumptionDeletion(subsumer, subsumee, substitution) => {
          if !premise.contains(subsumer) then
            report(s"""premise does not contain subsumer
                        |premise: $premise
                        |subsumer: $subsumer""".stripMargin)

          if !premise.contains(subsumee) then
            report(s"""premise does not contain subsumee
                        |premise: $premise
                        |subsumee: $subsumee""".stripMargin)

          if subsumer == subsumee then
            report(s"""subsumer and subsumee must be different
                        |subsumer: $subsumer
                        |subsumee: $subsumee""".stripMargin)

          val subsumerAfterSubstitution = substitution(subsumer)
          if !subsumerAfterSubstitution.isSubsetOf(subsumee) then
            report(s"""subsumer after substitution is not a subset of subsumee
                        |subsumer: $subsumer
                        |subsumee: $subsumee
                        |substitution: $substitution
                        |subsumer after substitution: $subsumerAfterSubstitution""".stripMargin)

          val expectedConclusion = premise - subsumee
          val missingClauses = expectedConclusion -- conclusion
          if missingClauses.nonEmpty then
            report(s"""conclusion is missing clauses
                        |conclusion: $conclusion
                        |expected conclusion: $expectedConclusion
                        |missing clauses: $missingClauses""".stripMargin)

          val unexpectedClauses = conclusion -- expectedConclusion
          if unexpectedClauses.nonEmpty then
            report(s"""conclusion contains unexpected clauses
                        |conclusion: $conclusion
                        |expected conclusion: $expectedConclusion
                        |unexpected clauses: $unexpectedClauses""".stripMargin)
        }

        case DerivationStep.PurifiedClauseDeletion(pointedClause) => {
          if !premise.contains(pointedClause.clause) then
            report(s"""premise does not contain pointed clause
                        |premise: $premise
                        |pointed clause: ${pointedClause.clause}""".stripMargin)

          val expectedConclusion = premise - pointedClause.clause
          val missingClauses = expectedConclusion -- conclusion
          if missingClauses.nonEmpty then
            report(s"""conclusion is missing clauses
                        |conclusion: $conclusion
                        |expected conclusion: $expectedConclusion
                        |missing clauses: $missingClauses""".stripMargin)

          val unexpectedClauses = conclusion -- expectedConclusion
          if unexpectedClauses.nonEmpty then
            report(s"""conclusion contains unexpected clauses
                        |conclusion: $conclusion
                        |expected conclusion: $expectedConclusion
                        |unexpected clauses: $unexpectedClauses""".stripMargin)

          if !isPurified(pointedClause, expectedConclusion) then
            report(s"""side condition violated: pointed clause is not purified in remaining clauses
                        |premise without pointed clause: $expectedConclusion
                        |pointed clause: $pointedClause""".stripMargin)
        }
      }
    }

    reasons.toSeq
  }

  def isDerivationStepCorrect(
      step: DerivationStep,
      premise: Set[HOLClause],
      conclusion: Set[HOLClause]
  ): Boolean =
    reasonsThatDerivationStepIsIncorrect(step, premise, conclusion).isEmpty

  def reasonsThatDerivationIsIncorrect(derivation: Derivation): Iterator[String] = {
    def go(derivation: Derivation, index: Int): Iterator[String] = {
      derivation.derivationSteps match {
        case Nil => Iterator.empty
        case step :: next =>
          val premise = derivation.from.firstOrderClauses
          val conclusion = step(premise)
          reasonsThatDerivationStepIsIncorrect(step, premise, conclusion).map(r =>
            s"""at step $index:
               |$r""".stripMargin
          ).iterator ++ go(derivation.tail, index + 1)
      }
    }

    go(derivation, 1)
  }

  def isDerivationCorrect(derivation: Derivation): Boolean =
    reasonsThatDerivationIsIncorrect(derivation).isEmpty
}
