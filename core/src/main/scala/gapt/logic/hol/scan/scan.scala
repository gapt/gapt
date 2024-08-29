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

object scan {
  case class ResolutionCandidate(clause: HOLClause, index: SequentIndex):
    def atom = clause(index)
    def args = atom match
      case Atom(_, args) => args

    def hoVar: Var = atom match
      case Atom(v @ Var(_, _), _) => v

    def abstracted: (ResolutionCandidate, Seq[FOLVar]) =
      val Atom(symbol @ Var(_, _), args) = this.atom: @unchecked
      val nameGen = rename.awayFrom(freeFOLVariables(clause))
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
    case Purification(candidate: ResolutionCandidate)

    def apply(clauses: Set[HOLClause]): Set[HOLClause] =
      this match
        case Resolution(left, right) =>
          val (leftAbstracted, leftVars) = left.abstracted
          val (rightAbstracted, _) = right.abstracted
          val resolvent = resolve(leftAbstracted, rightAbstracted)
          val resolventWithoutConstraints = eliminateConstraints(resolvent, leftVars.toSet).map { case a: Atom => a }
          clauses + resolventWithoutConstraints

        case Purification(candidate) => clauses - candidate.clause

  case class State(
      activeClauses: Set[HOLClause],
      activeCandidate: Option[(ResolutionCandidate, Set[ResolutionCandidate])],
      quantifiedVariables: Set[Var],
      derivation: Vector[(Set[HOLClause], Inference)]
  )

  def apply(input: Set[HOLClause], quantifiedVariables: Set[Var]): (Set[HOLClause], Substitution) =
    val state = saturate(State(input, None, quantifiedVariables, Vector.empty))
    (state.activeClauses, witnesses(state.derivation.toList, quantifiedVariables))

  def nextInference(state: State): Option[(Inference, State)] =
    state.activeCandidate match
      case None => {
        pickResolutionCandidate(state) match
          case None                      => None
          case Some(resolutionCandidate) => nextInference(state.copy(activeCandidate = Some((resolutionCandidate, Set.empty))))
      }
      case Some((resolutionCandidate, resolvedClauses)) => {
        pickResolutionPartner(resolutionCandidate, state.activeClauses, resolvedClauses) match
          case None                    => Some((Inference.Purification(resolutionCandidate), state))
          case Some(resolutionPartner) => Some((Inference.Resolution(resolutionCandidate, resolutionPartner), state))
      }

  def pickResolutionCandidate(state: State): Option[ResolutionCandidate] =
    state.activeClauses.flatMap { clause =>
      val index = clause.indicesWhere {
        case Atom(v @ Var(_, _), _) if state.quantifiedVariables.contains(v) => true
        case _                                                               => false
      }.headOption

      index.map(ResolutionCandidate(clause, _))
    }.headOption

  def pickResolutionPartner(activeCandidate: ResolutionCandidate, activeClauses: Set[HOLClause], resolvedCandidates: Set[ResolutionCandidate]): Option[ResolutionCandidate] =
    (activeClauses - activeCandidate.clause).flatMap { clause =>
      clause.cedent(!activeCandidate.index.polarity).zipWithIndex.filter {
        case (Atom(v @ Var(_, _), _), _) => activeCandidate.hoVar == v
        case _                           => false
      }.map { case (_, index) => (clause, SequentIndex(!activeCandidate.index.polarity, index)) }
    }.map { case (clause, index) => ResolutionCandidate(clause, index) }
      .filter { candidate => !resolvedCandidates.contains(candidate) }
      .headOption

  def saturate(state: State): State =
    val inference = nextInference(state)
    inference match
      case None => state
      case Some((inference @ Inference.Resolution(left, right), state)) => saturate(state.copy(
          activeClauses = inference(state.activeClauses),
          activeCandidate = state.activeCandidate.map { case (c, resolvedClauses) => (c, resolvedClauses + right) },
          derivation = state.derivation :+ (state.activeClauses, inference)
        ))
      case Some((inference @ Inference.Purification(candidate), state)) => saturate(state.copy(
          activeClauses = inference(state.activeClauses),
          activeCandidate = None,
          derivation = state.derivation :+ (state.activeClauses, inference)
        ))

  def argCount(v: Var) = v match {
    case Var(_, FunctionType(_, args)) => args.size
  }

  def witnesses(reverseDerivation: List[(Set[HOLClause], Inference)], quantifiedVariables: Set[Var]): Substitution =
    reverseDerivation match
      case head :: next => {
        head match
          case (_, Inference.Resolution(left, right)) => witnesses(next, quantifiedVariables)
          case (clauseSet, Inference.Purification(candidate)) => {

            val wits = witnesses(next, quantifiedVariables)

            val candidateOccurringClauses = clauseSet.filter { clause =>
              clause.exists {
                case Atom(v: Var, _) => quantifiedVariables.contains(v)
                case _               => false
              }
            }

            val witExtension: Substitution =
              if candidateOccurringClauses.forall { clause =>
                  clause.succedent.exists {
                    case Atom(v: Var, _) if candidate.hoVar == v => true
                    case _                                       => false
                  }
                }
              then {
                Substitution(candidate.hoVar, Abs.Block(rename.awayFrom(Iterable.empty).freshStream("u").take(argCount(candidate.hoVar)).map(FOLVar(_)), TopC()))
              } else if candidateOccurringClauses.forall { clause =>
                  clause.antecedent.exists {
                    case Atom(v: Var, _) if candidate.hoVar == v => true
                    case _                                       => false
                  }
                }
              then {
                Substitution(candidate.hoVar, Abs.Block(rename.awayFrom(Iterable.empty).freshStream("u").take(argCount(candidate.hoVar)).map(FOLVar(_)), BottomC()))
              } else {
                val Atom(symbol @ Var(_, _), _) = candidate.atom: @unchecked
                val reswit = resWitness(candidate)
                Substitution(symbol, reswit)
              }

            val composedWitnesses = wits.compose(witExtension)
            val betaNormalized = Substitution(composedWitnesses.map.view.mapValues(e => {
              val Abs.Block(vars, formula: Formula) = betaNormalize(e): @unchecked
              Abs.Block(vars, simplify(formula))
            }))
            betaNormalized
          }
      }
      case Nil => Substitution(quantifiedVariables.map {
          case v @ Var(_, FunctionType(To, args)) =>
            (v, Abs.Block(rename.awayFrom(Iterable.empty).freshStream("u").take(args.size).map(FOLVar(_)), BottomC()))
        }.toMap)

  private def freeFOLVariables(expr: HOLClause): Set[FOLVar] =
    (freeVariables(expr) -- freeHOVariables(expr.toFormula)).map { case v: FOLVar => v }

  def eliminateConstraints(clause: HOLSequent, keepVariables: Set[FOLVar]): HOLSequent =
    val constraint = clause.antecedent.zipWithIndex.flatMap {
      case (Eq(v @ FOLVar(_), t), i) if !keepVariables.contains(v) => Some((v, t, i))
      case (Eq(t, v @ FOLVar(_)), i) if !keepVariables.contains(v) => Some((v, t, i))
      case _                                                       => None
    }.headOption
    constraint match
      case None => clause
      case Some((v, t, i)) =>
        eliminateConstraints(Substitution(v, t)(clause.delete(Ant(i))), keepVariables)

  def saturateWithResolutionCandidate(candidate: ResolutionCandidate, resolventSet: Set[HOLClause], resolvedCandidates: Set[ResolutionCandidate]): Set[HOLClause] = {
    val partner = pickResolutionPartner(candidate, resolventSet, resolvedCandidates)

    partner match
      case None => resolventSet
      case Some(partner) => {
        val resolvent = resolve(candidate, partner)
        val resolventWithoutConstraints = eliminateConstraints(resolvent, candidate.args.map { case x: FOLVar => x }.toSet).map { case a: Atom => a }
        saturateWithResolutionCandidate(candidate, resolventSet + resolventWithoutConstraints, resolvedCandidates + partner)
      }
  }

  def resolve(left: ResolutionCandidate, right: ResolutionCandidate): HOLClause = {
    val renaming = rename(freeFOLVariables(left.clause), freeFOLVariables(right.clause))
    val rightClausesRenamed = Substitution(renaming)(right.clause).map { case a: Atom => a }
    val rightRenamed = ResolutionCandidate(rightClausesRenamed, right.index)
    val constraints = HOLClause(left.args.zip(rightRenamed.args).map(Eq(_, _)), Seq.empty)
    val resolvent = constraints ++ left.clause.delete(left.index) ++ rightRenamed.clause.delete(rightRenamed.index)
    resolvent
  }

  def resWitness(candidate: ResolutionCandidate): Expr = {
    val (abstractedResolutionCandidate, vars) = candidate.abstracted
    val resCandidate = eliminateConstraints(abstractedResolutionCandidate.clause, vars.toSet).map { case a: Atom => a }

    val resolventSet = saturateWithResolutionCandidate(abstractedResolutionCandidate, Set(HOLClause(Seq((abstractedResolutionCandidate.atom, !abstractedResolutionCandidate.index.polarity)))), Set.empty)

    val formula: Formula = abstractedResolutionCandidate.index.polarity match
      case Polarity(false) => And(resolventSet.map {
          clause => All.Block((freeFOLVariables(clause) -- vars).toSeq, clause.toDisjunction)
        })
      case Polarity(true) => Or(resolventSet.map {
          clause => Ex.Block((freeFOLVariables(clause) -- vars).toSeq, clause.toNegConjunction)
        })

    Abs(vars, formula)
  }
}
