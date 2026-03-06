package gapt.logic.hol

import gapt.expr._
import gapt.proofs.HOLClause
import gapt.expr.util.rename
import gapt.expr.util.freeVariables
import gapt.expr.subst.Substitution
import gapt.expr.formula.Atom
import gapt.expr.formula.fol.FOLVar
import gapt.proofs.RichFormulaSequent
import gapt.logic.Polarity
import gapt.expr.formula.Formula
import gapt.expr.formula.And
import gapt.expr.formula.Or
import gapt.expr.formula.All
import gapt.expr.formula.Ex
import gapt.expr.formula.Eq
import gapt.expr.BetaReduction.betaNormalize
import gapt.expr.ty.FunctionType
import gapt.expr.formula.constants.BottomC
import gapt.logic.hol.wdls.simplify
import gapt.expr.formula.constants.TopC
import gapt.expr.ty.Ty
import gapt.proofs.Sequent
import gapt.provers.escargot.Escargot
import gapt.expr.formula.Iff
import gapt.logic.hol.scan.{PointedClause, Derivation, DerivationStep}
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.Neg
import gapt.expr.given

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
    * Runs the SCAN algorithm multiple times on the input predicate elimination problem to find several derivations and returns the corresponding witnesses
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

  /**
    * Runs the SCAN algorithm multiple times on the input predicate elimination problem to find several derivations and corresponding witnesses and only gives back those that are mutually non-equivalent.
    *
    * @param substitutions an IterableOnce of the substitutions of which to filter out the mutually non-equivalent ones
    * @return an iterator of mutually non-equivalent substitutions satisfying the WSOQE-condition of the given input
    */
  def mutuallyNonEquivalentWitnesses(
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
    val witnesses = iterator.flatMap {
      case Left(_) => None
      case Right(derivation) =>
        witnessSubstitution(derivation, limit = witnessLimit)
          .map(simplifyWitnessSubstitution)
          .map(w => (derivation, w))
    }

    val (firstOrderEquivalent, firstWitness) = witnesses.nextOption() match {
      case None                    => return Iterator.empty
      case Some((derivation, wit)) => (derivation.conclusion.toFormula, wit)
    }
    return MutuallyNonEquivalentWitnessIterator(
      Iterator(firstWitness) ++ witnesses.map(_._2),
      firstOrderEquivalent
    )
  }

  private case class MutuallyNonEquivalentWitnessIterator(
      val witnessIterator: Iterator[Substitution],
      val firstOrderEquivalent: Formula
  ) extends Iterator[Substitution] {
    private val state: scala.collection.mutable.Set[Substitution] = scala.collection.mutable.Set.empty
    private var nextWitness: Option[Substitution] = None
    def hasNext: Boolean =
      try
        nextWitness = Some(next())
        true
      catch { case _: NoSuchElementException => false }
    def next(): Substitution = {
      nextWitness match {
        case Some(wit) => {
          nextWitness = None
          return wit
        }
        case None =>
      }

      val nextNonEquivalentWit = witnessIterator.filter(w =>
        state.forall(s => !areEquivalent(firstOrderEquivalent, w, s))
      )

      val nextWit = nextNonEquivalentWit.next()
      state.add(nextWit)
      nextWit
    }
  }

  private def witnessSubstitution(
      derivation: Derivation,
      limit: Option[Int]
  ): Option[Substitution] = {
    derivation.derivationSteps match {
      case Nil => Some(Substitution())
      case head :: next => {
        head match
          case i: (DerivationStep.ConstraintResolution |
                DerivationStep.ConstraintFactoring |
                DerivationStep.TautologyDeletion |
                DerivationStep.SubsumptionDeletion |
                DerivationStep.VariableElimination) => witnessSubstitution(derivation.tail, limit)

          case DerivationStep.ExtendendPurityDeletion(hoVar, polarity) => {
            val wits = witnessSubstitution(derivation.tail, limit)
            val argumentVariables = freshArgumentVariables(hoVar.ty, "u")
            val wit = if polarity.positive then TopC() else BottomC()
            val witSubst = Substitution(hoVar, Abs.Block(argumentVariables, wit))
            wits.map(w => w.compose(witSubst))
          }

          case DerivationStep.PurifiedClauseDeletion(candidate) => {
            val conclusion = head(derivation.from.firstOrderClauses)
            for
              w <- witnessSubstitution(derivation.tail, limit)
              ext <- purifiedClauseDeletionSubstitution(candidate, conclusion, limit)
            yield {
              w.compose(ext)
            }
          }
      }
    }
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

  def purifiedClauseDeletionSubstitution(
      pointedClause: PointedClause,
      clauseSet: Set[HOLClause],
      limit: Option[Int]
  ): Option[Substitution] = {
    val degree = minAcyclicPurificationDegree(pointedClause, clauseSet)
    if degree.isDefined then
      Some(acyclicWitness(pointedClause, degree.get))
    else
      lRes(pointedClause, limit).map {
        wit => Substitution((pointedClause.varOption.get, wit))
      }
  }

  type PurificationSubsumption = Map[PointedClause, HOLClause]
  def minAcyclicPurificationDegree(
      pointedClause: PointedClause,
      clauseSet: Set[HOLClause]
  ): Option[Int] = {
    (for
      subsumption <- purificationSubsumptions(clauseSet, pointedClause)
      degree <- acyclicDegree(clauseSet, pointedClause, subsumption)
    yield degree).minOption
  }

  def purificationSubsumptions(
      clauseSet: Set[HOLClause],
      pointedClause: PointedClause
  ): Seq[PurificationSubsumption] = {
    val subsumerCandidatesPerClause = scan.resolutionInferences(clauseSet, pointedClause).toSeq
      .map(inference => {
        val resolvent = scan.constraintResolvent(inference.left, inference.right)
        injectivelySubsumingClauses(pointedClause.symbol, !pointedClause.polarity, clauseSet, resolvent)
          .map(s => (inference.right, s)).toSeq
      })

    cartesianProduct(subsumerCandidatesPerClause).map(_.toMap).toSeq
  }

  private def cartesianProduct[A](xss: Seq[Seq[A]]): Iterator[Seq[A]] = {
    xss.foldLeft(Iterator(Seq.empty[A])) { (acc, xs) =>
      for {
        a <- acc
        x <- xs.iterator
      } yield a :+ x
    }
  }

  def injectivelySubsumingClauses(symbol: VarOrConst, polarity: Polarity, clauseSet: Set[HOLClause], clause: HOLClause): Set[HOLClause] = {
    clauseSet.filter(c => scan.isInjectivelySubsumedAfterVariableElimination(symbol, polarity, c, clause))
  }

  def acyclicDegree(
      clauseSet: Set[HOLClause],
      pointedClause: PointedClause,
      purificationSubsumption: PurificationSubsumption
  ): Option[Int] = {
    import scala.collection.mutable
    val degrees: mutable.Map[HOLClause, Int] = mutable.Map()

    def computeDegree(start: HOLClause, visited: Set[HOLClause]): Option[Int] = {
      if visited.contains(start) then
        // we've already visited this node, this means there is a path from
        // start to itself, i.e., the graph is cyclic, thus return None
        return None

      val computedDegree = degrees.get(start)
      if computedDegree.isDefined then
        return computedDegree
      else {
        val startPointedClauses = pointedClausesWithPolarity(start, pointedClause.symbol, !pointedClause.index.polarity)
        if startPointedClauses.isEmpty then
          degrees.update(start, 0)
          return Some(0)
        else
          val maxDegree = (for
            pointedClause <- startPointedClauses
            degree <- computeDegree(purificationSubsumption(pointedClause), visited + start)
          yield degree).maxOption

          if maxDegree.isEmpty then
            return None

          val startDegree = maxDegree.get + 1
          degrees.update(start, startDegree)
          return Some(startDegree)
      }
    }

    for clause <- clauseSet do
      computeDegree(clause, Set.empty)

    if !clauseSet.subsetOf(degrees.keySet) then
      // this means there are clauses that don't have associated degrees, i.e.,
      // clauses that are part of a cycle, i.e., the graph is cyclic
      None
    else
      degrees.values.maxOption
  }

  def pointedClausesWithPolarity(clause: HOLClause, symbol: VarOrConst, polarity: Polarity): Seq[PointedClause] = {
    clause.zipWithIndex.flatMap {
      case (Atom(head, _), index) if index.polarity == polarity && head == symbol => Seq(PointedClause(clause, index))
      case _                                                                      => Seq.empty
    }.elements.toSeq
  }

  def acyclicWitness(
      pointedClause: PointedClause,
      degree: Int
  ): Substitution = {
    val Abs.Block(vars, formula) = alpha(
      pointedClause,
      degree,
      Abs.Block(freshArgumentVariables(pointedClause.symbol.ty, "u"), BottomC())
    )
    val wit =
      if pointedClause.polarity.inAnt then
        formula
      else Neg(formula)

    Substitution((
      pointedClause.varOption.get,
      Abs.Block(vars, wit)
    ))
  }

  extension (e: Expr) {
    def simplified: Expr = {
      e.betaNormalized match {
        case Abs.Block(vars, f: Formula) => Abs.Block(vars, simplify(f))
      }
    }
  }

  import gapt.proofs.SequentIndex
  case class PointedClauseDecomposition(
      pointedAtom: Atom,
      pointedIndex: SequentIndex,
      oppositePolarityArgs: Sequent[List[Expr]],
      remainder: HOLClause
  )
  extension (pointedClause: PointedClause)
    def decomposition: PointedClauseDecomposition = {
      val (lit, rem) = pointedClause.clause.focus(pointedClause.index)
      val (reproduction, remainder) = rem.partition {
        case (Atom(head, _), p) => p == !pointedClause.index.polarity && head == pointedClause.symbol
        case _                  => ???
      }
      val reproductionArgs = reproduction.map { case Atom(_, args) => args }
      PointedClauseDecomposition(lit, pointedClause.index, reproductionArgs, remainder)
    }

  def alphaStep(P: PointedClause, placeholder: Var): Expr = {
    assert(P.varOption.isDefined)
    val freeFolVars = freeFOLVariables(P.clause.toFormula).toSeq
    val args = rename.awayFrom(freeFolVars).freshStream("u").zip(P.args).map {
      case (name, arg) => Var(name, arg.ty)
    }
    val PointedClauseDecomposition(_, _, reproductionArgs, remainder) = P.decomposition
    val reproductions = Sequent(Vector.empty[Atom], reproductionArgs.elements.map(args => Atom(placeholder, args)))
    val constraint = HOLClause(args.zip(P.args).map((a, b) => Eq(a, b)), Vector.empty[Atom])
    val firstClause = App(P.varOption.get, args).betaNormalized
    val formula: Formula = And(
      if P.index.isAnt then firstClause else Neg(firstClause),
      All.Block(freeFolVars, (constraint ++ remainder ++ reproductions).toFormula)
    ).betaNormalized
    Abs.Block(args, formula).simplified
  }

  def alpha(P: PointedClause, k: Int, initial: Expr): Expr = {
    val placeholder = rename.awayFrom(freeVariables(P.clause.toFormula)).fresh(Var("W", P.symbol.ty))
    if k == 0 then initial
    else {
      val previous = alpha(P, k - 1, initial)
      alphaStep(P, placeholder).substitute((placeholder, previous)).simplified
    }
  }

  def lRes(pointedClause: PointedClause, limit: Option[Int]): Option[Expr] = {
    val freshConstants = rename.awayFrom(containedNames(pointedClause.clause))
      .freshStream("c")
      .take(pointedClause.args.size)
      .map(FOLConst(_)).toList

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
    rename.awayFrom(blacklist).freshStream(varName).zip(argTypes).map(Var(_, _))
  }

  def areEquivalent(backgroundTheory: Formula, left: Substitution, right: Substitution): Boolean = {
    left.domain == right.domain && left.domain.forall(v => {
      val vars = freshArgumentVariables(v.ty, "u")
      val leftFormula = BetaReduction.betaNormalize(App(left(v), vars)).asInstanceOf[Formula]
      val rightFormula = BetaReduction.betaNormalize(App(right(v), vars)).asInstanceOf[Formula]
      Escargot.isValid(backgroundTheory --> Iff(leftFormula, rightFormula))
    })
  }
}
