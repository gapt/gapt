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
import gapt.logic.hol.scan.{PointedClause, Derivation, DerivationStep, constraintResolvent}
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.Neg

object wscan {
  def apply(
      input: ClauseSetPredicateEliminationProblem,
      oneSidedOnly: Boolean = true,
      allowResolutionOnBaseLiterals: Boolean = false,
      derivationLimit: Option[Int] = Some(100),
      attemptLimit: Option[Int] = Some(10),
      witnessLimit: Option[Int] = Some(2)
  ): Option[(Derivation, Substitution)] = {
    witnesses(input, oneSidedOnly, allowResolutionOnBaseLiterals, derivationLimit, attemptLimit, witnessLimit).nextOption()
  }

  def witnesses(input: ClauseSetPredicateEliminationProblem, oneSidedOnly: Boolean = true, allowResolutionOnBaseLiterals: Boolean = false, derivationLimit: Option[Int] = Some(100), attemptLimit: Option[Int] = Some(10), witnessLimit: Option[Int] = Some(2)): Iterator[(Derivation, Substitution)] = {
    val baseIterator = scan.derivationsFrom(
      input,
      oneSidedOnly = oneSidedOnly,
      allowResolutionOnBaseLiterals = allowResolutionOnBaseLiterals,
      derivationLimit = derivationLimit
    )
    val iterator = attemptLimit.map(l => baseIterator.take(l)).getOrElse(baseIterator)
    iterator.flatMap {
      case Left(_) => None
      case Right(derivation) =>
        val witnessOption = witnessSubstitution(derivation, limit = witnessLimit).map(simplifyWitnessSubstitution)
        witnessOption.map(w => (derivation, w))
    }
  }

  def witness(derivation: Derivation, witnessLimit: Option[Int] = Some(2)): Option[Substitution] = {
    witnessSubstitution(
      derivation,
      witnessLimit
    ).map(simplifyWitnessSubstitution)
  }

  def freshArgumentVariables(ty: Ty, varName: String, blacklist: Iterable[VarOrConst] = Iterable.empty) = {
    val FunctionType(_, argTypes) = ty: @unchecked
    rename.awayFrom(blacklist).freshStream("u").zip(argTypes).map(Var(_, _))
  }

  def witnessSubstitution(derivation: Derivation, limit: Option[Int]): Option[Substitution] = {
    def helper(derivation: Derivation): Option[Substitution] = {
      derivation.inferences match
        case head :: next => {
          head match
            case i: (DerivationStep.ConstraintResolution | DerivationStep.ConstraintFactoring | DerivationStep.TautologyDeletion | DerivationStep.SubsumptionDeletion | DerivationStep.ConstraintElimination) => helper(derivation.tail)
            case DerivationStep.ExtendendPurityDeletion(hoVar, polarity) => {
              val wits = helper(derivation.tail)
              val argumentVariables = freshArgumentVariables(hoVar.ty, "u")
              val wit = if polarity.positive then TopC() else BottomC()
              val witSubst = Substitution(hoVar, Abs.Block(argumentVariables, wit))
              wits.map(w => w.compose(witSubst))
            }
            case DerivationStep.PurifiedClauseDeletion(candidate) => {
              for
                w <- helper(derivation.tail)
                ext <- pResU(candidate, limit).map(Substitution(candidate.hoVar.asInstanceOf[Var], _))
              yield w.compose(ext)
            }
        }
        case Nil => Some(Substitution(derivation.initialPep.variablesToEliminate.map {
            case v @ Var(name, ty @ FunctionType(To, args)) =>
              val predicateVar = rename.awayFrom(containedNames(derivation.initialPep.clauses.toFormula)).fresh(Var(s"W$name", ty))
              (v, predicateVar)
          }.toMap))
    }

    helper(derivation)
  }

  def simplifyWitnessSubstitution(subst: Substitution): Substitution = {
    val betaNormalized = Substitution(subst.map.view.mapValues(e =>
      betaNormalize(e) match {
        case Abs.Block(vars, formula: Formula) => Abs.Block(vars, simplify(formula))
        case x                                 => x
      }
    ))
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

  def saturateWithResolutionCandidate(candidate: PointedClause, resolventSet: Set[HOLClause], resolvedCandidates: Set[PointedClause], limit: Option[Int]): Option[Set[HOLClause]] = {
    val partner = pickResolutionPartner(candidate, resolventSet, resolvedCandidates)

    partner match
      case None                                               => Some(resolventSet)
      case Some(partner) if limit.isDefined && limit.get <= 0 => None
      case Some(partner) => {
        val resolvent = constraintResolvent(candidate, partner)
        val resolventWithoutConstraints = eliminateConstraints(resolvent, candidate.args.map { case x: FOLVar => x }.toSet).map { case a: Atom => a }
        saturateWithResolutionCandidate(candidate, resolventSet + resolventWithoutConstraints, resolvedCandidates + partner, limit = limit.map(l => l - 1))
      }
  }

  def pickResolutionPartner(activeCandidate: PointedClause, activeClauses: Set[HOLClause], resolvedCandidates: Set[PointedClause]): Option[PointedClause] = {
    (activeClauses - activeCandidate.clause).flatMap { clause =>
      clause.cedent(!activeCandidate.index.polarity).zipWithIndex.filter {
        case (Atom(v, _), _) => activeCandidate.hoVar == v
        case _               => false
      }.map { case (_, index) => (clause, SequentIndex(!activeCandidate.index.polarity, index)) }
    }.map { case (clause, index) => PointedClause(clause, index) }
      .filter { candidate => !resolvedCandidates.contains(candidate) }
      .headOption
  }

  def pResU(pointedClause: PointedClause, limit: Option[Int]): Option[Expr] = {

    val freshConstants = rename.awayFrom(containedNames(pointedClause.clause)).freshStream("c").take(pointedClause.args.size).map(FOLConst(_)).toList

    val Atom(head, args) = pointedClause.atom: @unchecked
    val unitClause = HOLClause(Seq((Atom(head, freshConstants), !pointedClause.index.polarity)))
    val purificationResult = scan.purifyPointedClause(
      scan.State(
        activeClauses = Set(unitClause),
        derivation = scan.Derivation(ClauseSetPredicateEliminationProblem(Set(pointedClause.hoVar.asInstanceOf[Var]), Set(unitClause)), List.empty),
        derivationLimit = limit,
        oneSidedOnly = false,
        allowResolutionOnBaseLiterals = false
      ),
      pointedClause
    )

    purificationResult match
      case Left(_) => None
      case Right(state) => {
        val formula = pointedClause.index.polarity match
          case Polarity(false) => And(state.activeClauses.map {
              clause => All.Block((freeFOLVariables(clause.toFormula)).toSeq, clause.toDisjunction)
            })
          case Polarity(true) => Or(state.activeClauses.map {
              clause => Ex.Block((freeFOLVariables(clause.toFormula)).toSeq, clause.toNegConjunction)
            })
        val freshVars = rename.awayFrom(containedNames(formula)).freshStream("u").take(freshConstants.size).map(FOLVar(_)).toList
        val renaming = freshConstants.zip(freshVars).toMap

        Some(Abs(freshVars, renameFOLConstToFOLVar(formula, renaming)))
      }
  }

  def renameFOLConstToFOLVar(expr: Expr, renaming: Map[FOLConst, FOLVar]): Expr = {
    expr match
      case c: FOLConst      => renaming.get(c).getOrElse(c)
      case Neg(f)           => Neg(renameFOLConstToFOLVar(f, renaming))
      case And(left, right) => And(renameFOLConstToFOLVar(left, renaming), renameFOLConstToFOLVar(right, renaming))
      case Or(left, right)  => Or(renameFOLConstToFOLVar(left, renaming), renameFOLConstToFOLVar(right, renaming))

      case All(v, f) => All(v, renameFOLConstToFOLVar(f, renaming))
      case Ex(v, f)  => Ex(v, renameFOLConstToFOLVar(f, renaming))

      case App(left, right) => App(renameFOLConstToFOLVar(left, renaming), renameFOLConstToFOLVar(right, renaming))
      case Abs(v, f)        => Abs(v, renameFOLConstToFOLVar(f, renaming))
      case x                => x
  }
}
