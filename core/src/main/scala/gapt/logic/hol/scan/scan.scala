package gapt.logic.hol.scan

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

object scan {
  case class FormulaEquationClauseSet(quantifiedVariables: Set[Var], clauses: Set[HOLClause]):
    def toFormula: Formula = Ex.Block(quantifiedVariables.toSeq, clauses.toFormula)

  extension (clauseSet: Set[HOLClause])
    def toFormula: Formula = {
      val quantifierFreePart = And(clauseSet.map(_.toFormula))
      All.Block(freeFOLVariables(quantifierFreePart).toSeq, quantifierFreePart)
    }

  case class ResolutionCandidate(clause: HOLClause, index: SequentIndex):
    def atom = clause(index)
    def args = atom match
      case Atom(_, args) => args

    def hoVar: VarOrConst = atom match
      case Atom(v @ VarOrConst(_, _, _), _) => v

    def isVar: Boolean = hoVar match {
      case _: Var => true
      case _      => false
    }

    def abstracted: (ResolutionCandidate, Seq[FOLVar]) =
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
      (ResolutionCandidate(abstractedClause, sequentIndex), vars)

  enum Inference:
    case Resolution(left: ResolutionCandidate, right: ResolutionCandidate)
    case Factoring(clause: HOLClause, leftIndex: SequentIndex, rightIndex: SequentIndex)
    case Purification(candidate: ResolutionCandidate)
    case TautologyDeletion(tautology: HOLClause)
    case Subsumption(subsumer: HOLClause, subsumee: HOLClause, substitution: FOLSubstitution)
    case ConstraintElimination(clause: HOLClause, index: SequentIndex, substitution: FOLSubstitution)
    case Polarity(hoVar: Var, polarity: gapt.logic.Polarity)

    def apply(clauses: Set[HOLClause]): (Set[HOLClause], Set[HOLClause]) =
      this match
        case Resolution(left, right)                            => (Set(resolve(left, right)), Set.empty)
        case f: Factoring                                       => (Set(factor(f)), Set.empty)
        case Purification(candidate)                            => (Set.empty, Set(candidate.clause))
        case Subsumption(subsumer, subsumee, substitution)      => (Set.empty, Set(subsumee))
        case TautologyDeletion(clause)                          => (Set.empty, Set(clause))
        case ConstraintElimination(clause, index, substitution) => (Set(substitution(clause.delete(index)).map { case a: Atom => a }.distinct), Set(clause))
        case Polarity(hoVar, polarity) => {
          val removed = clauses.filter(c =>
            c.exists {
              case Atom(v: Var, _) if v == hoVar => true
              case _                             => false
            }
          )
          (Set.empty, removed)
        }

  def factor(factoring: Inference.Factoring): HOLClause = {
    val Inference.Factoring(clause, leftIndex, rightIndex) = factoring
    val Atom(_, leftArgs) = clause(leftIndex): @unchecked
    val Atom(_, rightArgs) = clause(rightIndex): @unchecked
    val constraints = leftArgs.zip(rightArgs).map(Eq(_, _))
    (clause.delete(rightIndex) ++ HOLClause(constraints, Seq.empty)).distinct
  }

  def isFactorOf(clause: HOLClause, other: HOLClause): Boolean = {
    factoringInferences(other).exists(i => factor(i) == clause)
  }

  def factoringInferences(clause: HOLClause): Set[Inference.Factoring] = {
    clause.succedent.zipWithIndex.combinations(2).flatMap {
      case Seq(left @ (Atom(leftHead, _), _: Int), right @ (Atom(rightHead, _), _: Int)) if leftHead == rightHead => Some((left, right))
      case _                                                                                                      => None
    }.map[Inference.Factoring] {
      case ((_, leftIndex), (_, rightIndex)) => Inference.Factoring(clause, Suc(leftIndex), Suc(rightIndex))
    }.toSet
  }

  case class State(
      activeClauses: Set[HOLClause],
      quantifiedVariables: Set[Var],
      derivation: Derivation,
      derivationLimit: Option[Int]
  )

  def apply(input: FormulaEquationClauseSet, derivationLimit: Option[Int] = Some(100), witnessLimit: Int = 100): Iterator[Either[Derivation, (Set[HOLClause], Option[Substitution], Derivation)]] =
    assert(derivationLimit.isEmpty || derivationLimit.get >= 0, "derivation limit must be non-negative")
    val states = saturate(State(
      input.clauses,
      input.quantifiedVariables,
      Derivation(input.clauses, List.empty),
      derivationLimit
    ))
    states.map { state =>
      val result =
        for
          s <- state
          wits = witnessSubstitution(s.derivation, input.quantifiedVariables, witnessLimit).map(simplifyWitnessSubstitution)
        yield (s.activeClauses, wits, s.derivation)
      result.left.map(state => state.derivation)
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

  def nextInference(state: State): Seq[Seq[Inference]] = {
    // check for appropriate polarity
    val polarity: Option[Inference.Polarity] = {
      state.quantifiedVariables.toSeq.flatMap[Inference.Polarity] { w =>
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
          p.map(Inference.Polarity(w, _))
      }.headOption
    }

    // check for tautologies
    val tautologyDeletion: Option[Inference.TautologyDeletion] = state.activeClauses.find(_.isTaut).map(Inference.TautologyDeletion(_))

    // check for eliminable constraints
    val constraintElimination: Option[Inference.ConstraintElimination] =
      (for
        clause <- state.activeClauses
        case (Eq(left, right), index) <- clause.antecedent.zipWithIndex
        subst <- syntacticMGU(left, right, freeHOVariables(left) ++ freeHOVariables(right)).map(_.asFOLSubstitution)
      yield (clause, Ant(index), subst)).map[Inference.ConstraintElimination](Inference.ConstraintElimination(_, _, _)).headOption

    // check for subsumption
    val subsumption: Option[Inference.Subsumption] = state.activeClauses.toSeq.combinations(2).flatMap {
      case Seq(left, right) => {
        val leftSubsumptions: Seq[Inference.Subsumption] = subsumptionSubstitution(left, right).toSeq.map(s => Inference.Subsumption(left, right, s))
        val rightSubsumptions: Seq[Inference.Subsumption] = subsumptionSubstitution(right, left).toSeq.map(s => Inference.Subsumption(right, left, s))
        leftSubsumptions ++ rightSubsumptions
      }
    }.nextOption()

    // do factoring
    val factoring: Option[Inference.Factoring] = state.activeClauses.flatMap(factoringInferences).filter {
      case f => !isRedundant(state.activeClauses, factor(f))
    }.headOption

    // check for purification
    val purifications: Seq[Inference.Purification] = resolutionCandidates(state.activeClauses).filter { rc =>
      rc.isVar && state.quantifiedVariables.contains(rc.hoVar.asInstanceOf[Var])
    }.flatMap[Inference.Purification] { rc =>
      val hoVar @ Var(_, _) = rc.hoVar: @unchecked
      val allFactorsRedundant = factoringInferences(rc.clause).forall {
        case inference: Inference.Factoring => isRedundant(state.activeClauses, factor(inference))
      }
      val allResolventsRedundant = resolutionInferences(rc, state.activeClauses - rc.clause).forall {
        case Inference.Resolution(left, right) => isRedundant(state.activeClauses, resolve(left, right))
      }
      val isAFactor = state.activeClauses.exists(c => isFactorOf(rc.clause, c))
      if !isAFactor && allFactorsRedundant && allResolventsRedundant
      then Some(Inference.Purification(rc))
      else None
    }.toSeq

    val singleInference = polarity.orElse(tautologyDeletion).orElse(constraintElimination).orElse(subsumption).orElse(factoring)

    val (inductivePurifications, nonInductivePurifications) = purifications.partition(i => isInductive(i.candidate))

    val activeClauseCandidates = state.activeClauses
      .flatMap(c => resolutionCandidates(c))
      .filter(c => !isInductive(c) && nonRedundantResolutionInferences(state.activeClauses, c).nonEmpty)

    val resolutionPossibilities: Seq[Seq[Inference.Resolution]] = activeClauseCandidates.toSeq.map { candidate =>
      nonRedundantResolutionInferences(state.activeClauses, candidate)
    }

    if singleInference.isDefined then Seq(singleInference.toSeq)
    else if singleInference.isEmpty && !nonInductivePurifications.isEmpty then
      nonInductivePurifications.map(Seq(_))
    else
      resolutionPossibilities
  }

  def nonRedundantResolutionInferences(clauses: Set[HOLClause], candidate: ResolutionCandidate) = {
    resolutionInferences(candidate, clauses - candidate.clause).filter {
      case Inference.Resolution(left, right) => !isRedundant(clauses, resolve(left, right))
    }.toSeq
  }

  def isInductive(candidate: ResolutionCandidate): Boolean = {
    candidate.clause.cedent(!candidate.index.polarity).exists {
      case Atom(v @ VarOrConst(_, _, _), _) if v == candidate.hoVar => true
      case _                                                        => false
    }
  }

  def resolutionCandidates(clause: HOLClause): Set[ResolutionCandidate] = {
    clause.indices.map(ResolutionCandidate(clause, _)).toSet
  }

  def resolutionCandidates(clauses: Set[HOLClause]): Set[ResolutionCandidate] = {
    clauses.flatMap(resolutionCandidates)
  }

  def resolutionInferences(resolutionCandidate: ResolutionCandidate, clauses: Set[HOLClause]): Set[Inference.Resolution] = {
    resolutionCandidates(clauses).filter {
      rc => rc.hoVar == resolutionCandidate.hoVar && rc.index.polarity == !resolutionCandidate.index.polarity
    }.map(rc => Inference.Resolution(resolutionCandidate, rc))
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
              val (added, removed) = inference(state.activeClauses)
              assert(added.intersect(removed).isEmpty)
              state.copy(
                activeClauses = (state.activeClauses ++ added) -- removed,
                derivation = state.derivation.copy(inferences = state.derivation.inferences :+ inference),
                derivationLimit = state.derivationLimit.map(d => d - 1)
              )
          }
          saturate(updatedState)
      }
  }

  def freshArgumentVariables(ty: Ty, varName: String, blacklist: Iterable[VarOrConst] = Iterable.empty) = {
    val FunctionType(_, argTypes) = ty: @unchecked
    rename.awayFrom(blacklist).freshStream("u").zip(argTypes).map(Var(_, _))
  }

  def witnessSubstitution(derivation: Derivation, quantifiedVariables: Set[Var], limit: Int): Option[Substitution] = {
    def helper(derivation: Derivation): Option[Substitution] = {
      derivation.inferences match
        case head :: next => {
          head match
            case i: (Inference.Resolution | Inference.Factoring | Inference.TautologyDeletion | Inference.Subsumption | Inference.ConstraintElimination) => helper(derivation.tail)
            case Inference.Polarity(hoVar, polarity) => {
              val wits = helper(derivation.tail)
              val argumentVariables = freshArgumentVariables(hoVar.ty, "u")
              val wit = if polarity.positive then TopC() else BottomC()
              val witSubst = Substitution(hoVar, Abs.Block(argumentVariables, wit))
              wits.map(w => w.compose(witSubst))
            }
            case Inference.Purification(candidate) => {
              val hoVar = candidate.hoVar.asInstanceOf[Var]
              val wits = helper(derivation.tail)

              val candidateOccurringClauses = derivation.initialClauseSet.filter { clause =>
                clause.exists {
                  case Atom(v: Var, _) => true
                  case _               => false
                }
              }
              val allCandidateOccuringClausesContainCandidatePositively = candidateOccurringClauses.forall { clause =>
                clause.succedent.exists {
                  case Atom(v: Var, _) if candidate.hoVar == v => true
                  case _                                       => false
                }
              }
              val allCandidateOccuringClausesContainCandidateNegatively = candidateOccurringClauses.forall { clause =>
                clause.antecedent.exists {
                  case Atom(v: Var, _) if candidate.hoVar == v => true
                  case _                                       => false
                }
              }

              val witExtension: Option[Substitution] =
                if allCandidateOccuringClausesContainCandidatePositively
                then {
                  val argumentVariables = freshArgumentVariables(candidate.hoVar.ty, "u")
                  Some(Substitution(hoVar, Abs.Block(argumentVariables, TopC())))
                } else if allCandidateOccuringClausesContainCandidateNegatively
                then {
                  val argumentVariables = freshArgumentVariables(candidate.hoVar.ty, "u")
                  Some(Substitution(hoVar, Abs.Block(argumentVariables, BottomC())))
                } else {
                  resWitness(candidate, limit).map(Substitution(hoVar, _))
                }

              for
                w <- wits
                ext <- witExtension
              yield w.compose(ext)
            }
        }
        case Nil => Some(Substitution(quantifiedVariables.map {
            case v @ Var(_, FunctionType(To, args)) =>
              (v, Abs.Block(rename.awayFrom(Iterable.empty).freshStream("u").take(args.size).map(FOLVar(_)), BottomC()))
          }.toMap))
    }

    helper(derivation)
  }

  def simplifyWitnessSubstitution(subst: Substitution): Substitution = {
    val betaNormalized = Substitution(subst.map.view.mapValues(e => {
      val Abs.Block(vars, formula: Formula) = betaNormalize(e): @unchecked
      Abs.Block(vars, simplify(formula))
    }))
    betaNormalized
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

  def saturateWithResolutionCandidate(candidate: ResolutionCandidate, resolventSet: Set[HOLClause], resolvedCandidates: Set[ResolutionCandidate], limit: Int): Option[Set[HOLClause]] = {
    val partner = pickResolutionPartner(candidate, resolventSet, resolvedCandidates)

    partner match
      case None                        => Some(resolventSet)
      case Some(partner) if limit <= 0 => None
      case Some(partner) => {
        val resolvent = resolve(candidate, partner)
        val resolventWithoutConstraints = eliminateConstraints(resolvent, candidate.args.map { case x: FOLVar => x }.toSet).map { case a: Atom => a }
        saturateWithResolutionCandidate(candidate, resolventSet + resolventWithoutConstraints, resolvedCandidates + partner, limit = limit - 1)
      }
  }

  def pickResolutionPartner(activeCandidate: ResolutionCandidate, activeClauses: Set[HOLClause], resolvedCandidates: Set[ResolutionCandidate]): Option[ResolutionCandidate] = {
    (activeClauses - activeCandidate.clause).flatMap { clause =>
      clause.cedent(!activeCandidate.index.polarity).zipWithIndex.filter {
        case (Atom(v, _), _) => activeCandidate.hoVar == v
        case _               => false
      }.map { case (_, index) => (clause, SequentIndex(!activeCandidate.index.polarity, index)) }
    }.map { case (clause, index) => ResolutionCandidate(clause, index) }
      .filter { candidate => !resolvedCandidates.contains(candidate) }
      .headOption
  }

  def resolve(left: ResolutionCandidate, right: ResolutionCandidate): HOLClause = {
    val renaming = rename(freeFOLVariables(left.clause.toFormula), freeFOLVariables(right.clause.toFormula))
    val rightClausesRenamed = Substitution(renaming)(right.clause).map { case a: Atom => a }
    val rightRenamed = ResolutionCandidate(rightClausesRenamed, right.index)
    val constraints = HOLClause(left.args.zip(rightRenamed.args).map(Eq(_, _)), Seq.empty)
    val resolvent = constraints ++ left.clause.delete(left.index) ++ rightRenamed.clause.delete(rightRenamed.index)
    resolvent.distinct
  }

  def resWitness(candidate: ResolutionCandidate, limit: Int): Option[Expr] = {
    val (abstractedResolutionCandidate, vars) = candidate.abstracted
    val resCandidate = eliminateConstraints(abstractedResolutionCandidate.clause, vars.toSet).map { case a: Atom => a }

    val saturationResult = saturateWithResolutionCandidate(abstractedResolutionCandidate, Set(HOLClause(Seq((abstractedResolutionCandidate.atom, !abstractedResolutionCandidate.index.polarity)))), Set.empty, limit)
    for
      resolventSet <- saturationResult
      formula: Formula = abstractedResolutionCandidate.index.polarity match
        case Polarity(false) => And(resolventSet.map {
            clause => All.Block((freeFOLVariables(clause.toFormula) -- vars).toSeq, clause.toDisjunction)
          })
        case Polarity(true) => Or(resolventSet.map {
            clause => Ex.Block((freeFOLVariables(clause.toFormula) -- vars).toSeq, clause.toNegConjunction)
          })
    yield Abs(vars, formula)
  }

  case class Derivation(initialClauseSet: Set[HOLClause], inferences: List[Inference]):
    def tail: Derivation = inferences match
      case head :: next => {
        val (added, removed) = head(initialClauseSet)
        Derivation(initialClauseSet ++ added -- removed, next)
      }
      case Nil => ???

}
