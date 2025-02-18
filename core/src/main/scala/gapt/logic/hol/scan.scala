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
import gapt.logic.hol.dls.simplify
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

    def abstracted: (PointedClause, Seq[FOLVar]) =
      val Atom(symbol @ VarOrConst(_, _, _), args) = this.atom: @unchecked
      val nameGen = rename.awayFrom(freeFOLVariables(clause.toFormula))
      val vars = nameGen.freshStream("u").take(args.size).map(FOLVar(_)).to(Seq)
      val constraints = HOLClause(vars.zip(args).map(Eq(_, _)), Seq.empty)
      val abstractedAtom = Atom(symbol, vars.toList)
      val abstractedClause: HOLClause =
        eliminateConstraints(
          constraints
            ++ clause.delete(index)
            ++ HOLClause(Seq((abstractedAtom, index.polarity))),
          vars.toSet
        ).map { case a: Atom => a }
      val idx = abstractedClause.cedent(index.polarity).indexOf(abstractedAtom)
      val sequentIndex = SequentIndex(index.polarity, idx)
      (PointedClause(abstractedClause, sequentIndex), vars)

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

  case class Derivation(initialClauseSet: Set[HOLClause], inferences: List[DerivationStep]):
    def tail: Derivation = inferences match
      case head :: next => Derivation(head(initialClauseSet), next)
      case Nil          => throw UnsupportedOperationException("tail of empty derivation")

    def conclusion: Set[HOLClause] = inferences match
      case Nil          => initialClauseSet
      case head :: next => Derivation(head(initialClauseSet), next).conclusion

  case class State(
      activeClauses: Set[HOLClause],
      quantifiedVariables: Set[Var],
      derivation: Derivation,
      derivationLimit: Option[Int]
  )

  def apply(input: ClauseSetPredicateEliminationProblem, derivationLimit: Option[Int] = Some(100), witnessLimit: Int = 100): Iterator[Either[Derivation, Derivation]] =
    assert(derivationLimit.isEmpty || derivationLimit.get >= 0, "derivation limit must be non-negative")
    val states = saturate(State(
      input.clauses,
      input.variablesToEliminate,
      Derivation(input.clauses, List.empty),
      derivationLimit
    ))
    states.map {
      state => state.map(_.derivation).left.map(_.derivation)
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
    // check for appropriate polarity
    val polarity: Option[DerivationStep.ExtendendPurityDeletion] = {
      state.quantifiedVariables.toSeq.flatMap[DerivationStep.ExtendendPurityDeletion] { w =>
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

    // do factoring
    val factoring: Option[DerivationStep.ConstraintFactoring] = state.activeClauses.flatMap(factoringInferences).filter {
      case f => !isRedundant(state.activeClauses, factor(f))
    }.headOption

    // check for purification
    val purifications: Seq[DerivationStep.PurifiedClauseDeletion] = pointedClauses(state.activeClauses).filter { rc =>
      rc.isVar && state.quantifiedVariables.contains(rc.hoVar.asInstanceOf[Var])
    }.flatMap[DerivationStep.PurifiedClauseDeletion] { rc =>
      val hoVar @ Var(_, _) = rc.hoVar: @unchecked
      val allFactorsRedundant = factoringInferences(rc.clause).forall {
        case inference: DerivationStep.ConstraintFactoring => isRedundant(state.activeClauses, factor(inference))
      }
      val allResolventsRedundant = resolutionInferences(rc, state.activeClauses - rc.clause).forall {
        case DerivationStep.ConstraintResolution(left, right) => isRedundant(state.activeClauses, constraintResolvent(left, right))
      }
      val isAFactor = state.activeClauses.exists(c => isFactorOf(rc.clause, c))
      if !isAFactor && allFactorsRedundant && allResolventsRedundant
      then Some(DerivationStep.PurifiedClauseDeletion(rc))
      else None
    }.toSeq

    val singleInference = polarity.orElse(tautologyDeletion).orElse(constraintElimination).orElse(subsumption).orElse(factoring)

    val (inductivePurifications, nonInductivePurifications) = purifications.partition(i => isInductive(i.candidate))

    val activeClauseCandidates = state.activeClauses
      .flatMap(c => pointedClauses(c))
      .filter(c => !isInductive(c) && nonRedundantResolutionInferences(state.activeClauses, c).nonEmpty)

    val resolutionPossibilities: Seq[Seq[DerivationStep.ConstraintResolution]] = activeClauseCandidates.toSeq.map { candidate =>
      nonRedundantResolutionInferences(state.activeClauses, candidate)
    }

    if singleInference.isDefined then Seq(singleInference.toSeq)
    else if singleInference.isEmpty && !nonInductivePurifications.isEmpty then
      nonInductivePurifications.map(Seq(_))
    else
      resolutionPossibilities
  }

  def nonRedundantResolutionInferences(clauses: Set[HOLClause], candidate: PointedClause) = {
    resolutionInferences(candidate, clauses - candidate.clause).filter {
      case DerivationStep.ConstraintResolution(left, right) => !isRedundant(clauses, constraintResolvent(left, right))
    }.toSeq
  }

  def isInductive(candidate: PointedClause): Boolean = {
    candidate.clause.cedent(!candidate.index.polarity).exists {
      case Atom(v @ VarOrConst(_, _, _), _) if v == candidate.hoVar => true
      case _                                                        => false
    }
  }

  def pointedClauses(clause: HOLClause): Set[PointedClause] = {
    clause.indices.map(PointedClause(clause, _)).toSet
  }

  def pointedClauses(clauses: Set[HOLClause]): Set[PointedClause] = {
    clauses.flatMap(pointedClauses)
  }

  def resolutionInferences(resolutionCandidate: PointedClause, clauses: Set[HOLClause]): Set[DerivationStep.ConstraintResolution] = {
    pointedClauses(clauses).filter {
      rc => rc.hoVar == resolutionCandidate.hoVar && rc.index.polarity == !resolutionCandidate.index.polarity
    }.map(rc => DerivationStep.ConstraintResolution(resolutionCandidate, rc))
  }

  def saturate(state: State): Iterator[Either[State, State]] = {
    val possibilities = nextInference(state)
    if possibilities.isEmpty then Iterator(Right(state))
    else
      possibilities.iterator.flatMap { inferences =>
        if !inferences.isEmpty && state.derivationLimit.isDefined && state.derivationLimit.get <= 0 then LazyList(Left(state))
        else if inferences.isEmpty then Iterator(Right(state))
        else
          val updatedState = inferences.foldLeft(state) {
            case (state, inference) =>
              state.copy(
                activeClauses = inference(state.activeClauses),
                derivation = state.derivation.copy(inferences = state.derivation.inferences :+ inference),
                derivationLimit = state.derivationLimit.map(d => d - 1)
              )
          }
          saturate(updatedState)
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
    val renaming = rename(freeFOLVariables(left.clause.toFormula), freeFOLVariables(right.clause.toFormula))
    val rightClausesRenamed = Substitution(renaming)(right.clause).map { case a: Atom => a }
    val rightRenamed = PointedClause(rightClausesRenamed, right.index)
    val constraints = HOLClause(left.args.zip(rightRenamed.args).map(Eq(_, _)), Seq.empty)
    val resolvent = constraints ++ left.clause.delete(left.index) ++ rightRenamed.clause.delete(rightRenamed.index)
    resolvent.distinct
  }
}
