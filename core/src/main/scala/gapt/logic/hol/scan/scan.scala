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

object scan:
  case class ResolutionCandidate(clause: HOLClause, index: SequentIndex):
    def atom = clause(index)
    def hoVar: Var = atom match
      case Atom(v @ Var(_, _), _) => v

  enum Inference:
    case Resolution(left: ResolutionCandidate, right: ResolutionCandidate)
    case Purification(candidate: ResolutionCandidate)

    def apply(clauses: Set[HOLClause]): Set[HOLClause] =
      this match
        case Resolution(left, right) =>
          val renaming = Substitution(rename(freeFOLVariables(right.clause), freeFOLVariables(left.clause)))
          val rightClausesRenamed = renaming(right.clause).map { case a: Atom => a }
          val rightRenamed = ResolutionCandidate(rightClausesRenamed, right.index)
          // val unifier =
          //   syntacticMGU(left.clause(left.index), rightRenamed(right.index), freeHOVariables(left.clause.toFormula) ++ freeHOVariables(right.clause.toFormula))
          val Atom(_, leftArgs) = left.atom: @unchecked
          val Atom(_, rightArgs) = rightRenamed.atom: @unchecked
          val constraints = HOLClause(leftArgs.zip(rightArgs).map((l, r) => Eq(l, r)), Seq.empty)

          val resolvent = eliminateConstraints((constraints ++ left.clause.delete(left.index) ++ rightRenamed.clause.delete(rightRenamed.index))).map { case a: Atom => a }
          clauses + resolvent

        case Purification(candidate) => clauses - candidate.clause

  case class State(
      activeClauses: Set[HOLClause],
      activeCandidate: Option[(ResolutionCandidate, Set[ResolutionCandidate])],
      quantifiedVariables: Set[Var],
      derivation: Vector[Inference]
  )

  def apply(input: Set[HOLClause], quantifiedVariables: Set[Var]): (Set[HOLClause], Substitution) =
    val state = saturate(State(input, None, quantifiedVariables, Vector.empty))
    (state.activeClauses, witnesses(state.derivation.reverse.toList))

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
    // println(s"state: $state")
    val inference = nextInference(state)
    // println(s"next inference: ${inference.map(_._1)}")
    // scala.io.StdIn.readLine()
    inference match
      case None => state
      case Some((inference @ Inference.Resolution(left, right), state)) => saturate(state.copy(
          activeClauses = inference(state.activeClauses),
          activeCandidate = state.activeCandidate.map { case (c, resolvedClauses) => (c, resolvedClauses + right) },
          derivation = state.derivation :+ inference
        ))
      case Some((inference @ Inference.Purification(candidate), state)) => saturate(state.copy(
          activeClauses = inference(state.activeClauses),
          activeCandidate = None,
          derivation = state.derivation :+ inference
        ))

  def witnesses(reverseDerivation: List[Inference]): Substitution =
    reverseDerivation match
      case head :: next => {
        head match
          case Inference.Resolution(left, right) => witnesses(next)
          case Inference.Purification(candidate) => {
            val wits = witnesses(next)
            val Atom(symbol @ Var(_, _), _) = candidate.atom: @unchecked
            val subst = Substitution(symbol, resWitness(candidate))

            // todo: beta normalization
            subst.compose(wits)
          }
      }
      case Nil => Substitution()

  private def freeFOLVariables(expr: HOLClause): Set[FOLVar] =
    (freeVariables(expr) -- freeHOVariables(expr.toFormula)).map { case v: FOLVar => v }

  def eliminateConstraints(clause: HOLSequent): HOLSequent =
    val constraint = clause.antecedent.zipWithIndex.flatMap {
      case (Eq(v @ Var(_, _), t), i) => Some((v, t, i))
      case (Eq(t, v @ Var(_, _)), i) => Some((v, t, i))
      case _                         => None
    }.headOption
    constraint match
      case None => clause
      case Some((v, t, i)) =>
        eliminateConstraints(Substitution(v, t)(clause.delete(Ant(i))))

  def resWitness(candidate: ResolutionCandidate): Expr = {
    val Atom(symbol @ Var(_, _), args) = candidate.atom: @unchecked
    val nameGen = rename.awayFrom(freeFOLVariables(candidate.clause))
    val vars = nameGen.freshStream("u").take(args.size).map(FOLVar(_)).to(Seq)
    val constraints = HOLClause(vars.zip(args).map((l, r) => Eq(l, r)), Seq.empty)
    val abstractedAtom = Atom(symbol, vars.toList)
    val abstractedClause =
      constraints
        ++ candidate.clause.delete(candidate.index)
        ++ HOLClause(Seq((abstractedAtom, candidate.index.polarity)))
    val index = abstractedClause.cedent(candidate.index.polarity).indexOf(abstractedAtom)
    val sequentIndex = SequentIndex(candidate.index.polarity, index)
    val abstractedResolutionCandidate = ResolutionCandidate(abstractedClause, sequentIndex)

    def saturateWithResolutionCandidate(candidate: ResolutionCandidate, resolventSet: Set[HOLClause], resolvedCandidates: Set[ResolutionCandidate]): Set[HOLClause] = {
      val partner = pickResolutionPartner(candidate, resolventSet, resolvedCandidates)

      partner match
        case None => resolventSet
        case Some(partner) => {
          val renaming = Substitution(rename(freeFOLVariables(partner.clause), freeFOLVariables(candidate.clause)))
          val rightClausesRenamed = renaming(partner.clause).map { case a: Atom => a }
          val rightRenamed = ResolutionCandidate(rightClausesRenamed, partner.index)
          val Atom(_, leftArgs) = candidate.atom: @unchecked
          val Atom(_, rightArgs) = rightRenamed.atom: @unchecked
          val constraints = HOLClause(leftArgs.zip(rightArgs).map((l, r) => Eq(l, r)), Seq.empty)

          val resolvent = eliminateConstraints((constraints ++ candidate.clause.delete(candidate.index) ++ rightRenamed.clause.delete(rightRenamed.index))).map { case a: Atom => a }
          saturateWithResolutionCandidate(candidate, resolventSet + resolvent, resolvedCandidates + partner)
        }
    }

    val resolventSet = saturateWithResolutionCandidate(abstractedResolutionCandidate, Set(HOLClause(Seq((abstractedResolutionCandidate.atom, !abstractedResolutionCandidate.index.polarity)))), Set.empty)

    val formula: Formula = candidate.index.polarity match
      case Polarity(false) => And(resolventSet.map {
          clause => All.Block((freeFOLVariables(clause) -- vars).toSeq, clause.toDisjunction)
        })
      case Polarity(true) => Or(resolventSet.map {
          clause => Ex.Block((freeFOLVariables(clause) -- vars).toSeq, clause.toNegConjunction)
        })

    Abs(vars, formula)
  }
