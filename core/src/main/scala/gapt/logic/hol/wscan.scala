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
import gapt.logic.hol.scan.{PointedClause, Derivation, DerivationStep, constraintResolvent}
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.Neg

object wscan {

  /**
    * Runs WSCAN algorithm on the input predicate elimination problem by running SCAN and attempting to find a WSOQE-witness for the input from a terminating derivation.
    *
    * @param input input predicate elimination problem in clause set form
    * @param oneSidedOnly @see oneSidedOnly option of scan
    * @param allowResolutionOnBaseLiterals @see allowResolutiononBaseLiterals option of scan
    * @param derivationLimit @see derivationLimit option of scan
    * @param attemptLimit @see attemptLimit option of scan
    * @param witnessLimit controls the amount of inferences to be performed during the saturation process to construct witnesses
    * @return a substitution satisfying the WSOQE-condition, if successful. Returns None otherwise
    */
  def apply(
      input: ClauseSetPredicateEliminationProblem,
      oneSidedOnly: Boolean = true,
      allowResolutionOnBaseLiterals: Boolean = false,
      derivationLimit: Option[Int] = Some(100),
      attemptLimit: Option[Int] = Some(100),
      witnessLimit: Option[Int] = Some(10)
  ): Option[Substitution] = {
    witnesses(input, oneSidedOnly, allowResolutionOnBaseLiterals, derivationLimit, attemptLimit, witnessLimit).nextOption()
  }

  /**
    * Runs the SCAN algorithm multiple times on the input predicate elimination problem to find several derivations returns the corresponding witnesses
    *
    * @param input input predicate elimination problem in clause set form
    * @param oneSidedOnly @see oneSidedOnly option of scan
    * @param allowResolutionOnBaseLiterals @see allowResolutiononBaseLiterals option of scan
    * @param derivationLimit @see derivationLimit option of scan
    * @param attemptLimit @see attemptLimit option of scan
    * @param witnessLimit @see witnessLimit option of wscan
    * @return an iterator of substitutions satisfying the WSOQE-condition of the given input
    */
  def witnesses(
      input: ClauseSetPredicateEliminationProblem,
      oneSidedOnly: Boolean = true,
      allowResolutionOnBaseLiterals: Boolean = false,
      derivationLimit: Option[Int] = Some(100),
      attemptLimit: Option[Int] = Some(100),
      witnessLimit: Option[Int] = Some(10)
  ): Iterator[Substitution] = {
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
        witnessSubstitution(derivation, limit = witnessLimit)
          .map(simplifyWitnessSubstitution)
    }
  }

  /**
    * Runs the SCAN algorithm multiple times on the input predicate elimination problem to find several derivations and corresponding witnesses and only gives back those that are mutually non-equivalent.
    *
    * @param substitutions an IterableOnce of the substitutions of which to filter out the mutually non-equivalent ones
    * @return an iterator of mutually non-equivalent substitutions satisfying the WSOQE-condition of the given input
    */
  def mutuallyNonEquivalent(
      substitutions: IterableOnce[Substitution]
  ): Iterator[Substitution] = {
    Iterator.unfold((Set.empty[Substitution], substitutions.iterator)) {
      case (state, iterator) => {
        val nextNonEquivalentWit = iterator.find(w => state.forall(s => !areEquivalent(w, s)))
        if nextNonEquivalentWit.isEmpty then
          None
        else
          Some((
            nextNonEquivalentWit.get,
            (state + nextNonEquivalentWit.get, iterator)
          ))
      }
    }
  }

  /**
    * Computes the WSCAN witness based on a given SCAN derivation.
    * Returns Some, if the computation succeeds with the given witnessLimit.
    * Returns None otherwise.
    *
    * @param derivation derivation based on which a witness should be computed
    * @param witnessLimit maximum number of inferences used in each saturation process to compute a witness. If set to None, the method might not terminate
    * @return an iterator eliminating derivation from the input clause set and a substitution satisfying the WSOQE-condition, if successful
    */
  def witness(
      derivation: Derivation,
      witnessLimit: Option[Int] = Some(1)
  ): Option[Substitution] = {
    witnessSubstitution(
      derivation,
      witnessLimit
    ).map(simplifyWitnessSubstitution)
  }

  private def witnessSubstitution(
      derivation: Derivation,
      limit: Option[Int]
  ): Option[Substitution] = {
    def helper(derivation: Derivation): Option[Substitution] = {
      derivation.derivationSteps match
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
                ext <- pResU(candidate, limit).map(Substitution(candidate.varOption.get, _))
              yield w.compose(ext)
            }
        }
        case Nil => Some(Substitution(derivation.from.varsToEliminate.map {
            case v @ Var(name, ty @ FunctionType(To, args)) =>
              val predicateVar = rename.awayFrom(containedNames(derivation.from.firstOrderClauses.toFormula)).fresh(Var(s"W$name", ty))
              (v, predicateVar)
          }.toMap))
    }

    helper(derivation)
  }

  private def simplifyWitnessSubstitution(subst: Substitution): Substitution = {
    val betaNormalized = Substitution(subst.map.view.mapValues(e =>
      betaNormalize(e) match {
        case Abs.Block(vars, formula: Formula) => Abs.Block(vars, simplify(formula))
        case x                                 => x
      }
    ))
    betaNormalized
  }

  private def freeFOLVariables(expr: Expr): Set[FOLVar] =
    (freeVariables(expr) -- freeHOVariables(expr)).map { case v: FOLVar => v }

  def pResU(pointedClause: PointedClause, limit: Option[Int]): Option[Expr] = {

    val freshConstants = rename.awayFrom(containedNames(pointedClause.clause)).freshStream("c").take(pointedClause.args.size).map(FOLConst(_)).toList

    val Atom(head, args) = pointedClause.designatedLiteral: @unchecked
    val unitClause = HOLClause(Seq((Atom(head, freshConstants), !pointedClause.index.polarity)))
    val purificationResult = scan.purifyPointedClause(
      scan.State.initialFrom(
        ClauseSetPredicateEliminationProblem(
          Seq(pointedClause.varOption.get),
          Set(unitClause)
        ),
        remainingAllowedInferences = limit,
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

  private def renameFOLConstToFOLVar(expr: Expr, renaming: Map[FOLConst, FOLVar]): Expr = {
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

  private def freshArgumentVariables(ty: Ty, varName: String, blacklist: Iterable[VarOrConst] = Iterable.empty) = {
    val FunctionType(_, argTypes) = ty: @unchecked
    rename.awayFrom(blacklist).freshStream("u").zip(argTypes).map(Var(_, _))
  }

  private def areEquivalent(left: Substitution, right: Substitution): Boolean = {
    left.domain == right.domain && left.domain.forall(v => {
      val vars = freshArgumentVariables(v.ty, "u")
      val leftFormula = BetaReduction.betaNormalize(App(left(v), vars)).asInstanceOf[Formula]
      val rightFormula = BetaReduction.betaNormalize(App(right(v), vars)).asInstanceOf[Formula]
      Escargot.isValid(Iff(leftFormula, rightFormula))
    })
  }
}
