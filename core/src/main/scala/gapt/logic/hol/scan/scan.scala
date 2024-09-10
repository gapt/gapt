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
  case class FormulaEquationClauseSet(quantifiedVariables: Set[Var], clauses: Set[HOLClause])

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
    case Purification(hoVar: Var, candidate: ResolutionCandidate)
    case TautologyDeletion(tautology: HOLClause)
    case Subsumption(subsumer: HOLClause, subsumee: HOLClause, substitution: FOLSubstitution)
    case ConstraintElimination(clause: HOLClause, index: SequentIndex, substitution: FOLSubstitution)

    def apply(clauses: Set[HOLClause]): (Set[HOLClause], Set[HOLClause]) =
      this match
        case Resolution(left, right)                            => (Set(resolve(left, right)), Set.empty)
        case f: Factoring                                       => (Set(factor(f)), Set.empty)
        case Purification(_, candidate)                         => (Set.empty, Set(candidate.clause))
        case Subsumption(subsumer, subsumee, substitution)      => (Set.empty, Set(subsumee))
        case TautologyDeletion(clause)                          => (Set.empty, Set(clause))
        case ConstraintElimination(clause, index, substitution) => (Set(substitution(clause.delete(index)).map { case a: Atom => a }.distinct), Set(clause))

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
      activeCandidates: scala.collection.mutable.Queue[ResolutionCandidate],
      quantifiedVariables: Set[Var],
      derivation: Derivation,
      derivationLimit: Option[Int]
  )

  def apply(input: FormulaEquationClauseSet, derivationLimit: Option[Int] = Some(100)): Either[Derivation, (Set[HOLClause], Substitution, Derivation)] =
    assert(derivationLimit.isEmpty || derivationLimit.get >= 0, "derivation limit must be non-negative")
    val result =
      for
        state <- saturate(State(
          input.clauses,
          scala.collection.mutable.Queue.from(resolutionCandidates(input.clauses)),
          input.quantifiedVariables,
          Derivation(input.clauses, List.empty),
          derivationLimit
        ))
        wits = simplifyWitnessSubstitution(witnessSubstitution(state.derivation, input.quantifiedVariables))
      yield (state.activeClauses, wits, state.derivation)
    result.left.map(state => state.derivation)

  def subsumptionSubstitution(subsumer: HOLClause, subsumee: HOLClause): Option[FOLSubstitution] = {
    val subsumerHoVarsAsConsts = subsumer.map { case Atom(VarOrConst(v, ty, tys), args) => Atom(Const(v, ty, tys), args) }
    val subsumeeHoVarsAsConsts = subsumee.map { case Atom(VarOrConst(v, ty, tys), args) => Atom(Const(v, ty, tys), args) }
    clauseSubsumption(subsumerHoVarsAsConsts, subsumeeHoVarsAsConsts, multisetSubsumption = true).map(_.asFOLSubstitution)
  }

  def isRedundant(clauses: Set[HOLClause], clause: HOLClause): Boolean = {
    val eliminatedConstraints = eliminateConstraints(clause, Set.empty)
    eliminatedConstraints.isTaut
    || clauses.exists(c => subsumptionSubstitution(c, eliminatedConstraints).isDefined)
  }

  def nextInference(state: State): Option[Inference] = {
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

    // check for purification
    val purification: Option[Inference.Purification] = resolutionCandidates(state.activeClauses).filter { rc =>
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
      then Some(Inference.Purification(hoVar, rc))
      else None
    }.headOption

    // do factoring
    val factoring: Option[Inference.Factoring] = state.activeClauses.flatMap(factoringInferences).filter {
      case f => !isRedundant(state.activeClauses, factor(f))
    }.headOption

    // do resolution
    tautologyDeletion.orElse(constraintElimination).orElse(subsumption).orElse(purification).orElse(factoring).orElse {
      var inference: Option[Inference.Resolution] = None
      while inference == None && !state.activeCandidates.isEmpty do {
        val candidate = state.activeCandidates.dequeue()

        if state.activeClauses.contains(candidate.clause) then {
          inference = resolutionInferences(candidate, state.activeClauses - candidate.clause).find {
            case Inference.Resolution(left, right) => !isRedundant(state.activeClauses, resolve(left, right))
          }
        }
      }
      inference
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

  def saturate(state: State): Either[State, State] = {
    val inference = nextInference(state)
    if inference.isDefined && state.derivationLimit.isDefined && state.derivationLimit.get <= 0 then Left(state)
    else
      inference match
        case None => Right(state)
        case Some(inference: Inference.Resolution) => {
          val (added, removed) = inference(state.activeClauses)
          assert(added.intersect(removed).isEmpty)
          val newCandidates = resolutionCandidates(added)
          state.activeCandidates.enqueueAll(newCandidates)
          state.activeCandidates.enqueue(inference.left)
          saturate(state.copy(
            activeClauses = (state.activeClauses ++ added) -- removed,
            derivation = state.derivation.copy(inferences = state.derivation.inferences :+ inference),
            derivationLimit = state.derivationLimit.map(d => d - 1)
          ))
        }
        case Some(inference) => {
          val (added, removed) = inference(state.activeClauses)
          assert(added.intersect(removed).isEmpty)
          val newCandidates = resolutionCandidates(added)
          state.activeCandidates.enqueueAll(newCandidates)
          saturate(state.copy(
            activeClauses = (state.activeClauses ++ added) -- removed,
            derivation = state.derivation.copy(inferences = state.derivation.inferences :+ inference),
            derivationLimit = state.derivationLimit.map(d => d - 1)
          ))
        }
  }

  def freshArgumentVariables(ty: Ty, varName: String, blacklist: Iterable[VarOrConst] = Iterable.empty) = {
    val FunctionType(_, argTypes) = ty: @unchecked
    rename.awayFrom(blacklist).freshStream("u").zip(argTypes).map(Var(_, _))
  }

  def witnessSubstitution(derivation: Derivation, quantifiedVariables: Set[Var]): Substitution = {
    def helper(derivation: Derivation): Substitution = {
      derivation.inferences match
        case head :: next => {
          head match
            case i: (Inference.Resolution | Inference.Factoring | Inference.TautologyDeletion | Inference.Subsumption | Inference.ConstraintElimination) => helper(derivation.tail)
            case Inference.Purification(hoVar, candidate) => {
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

              val witExtension: Substitution =
                if allCandidateOccuringClausesContainCandidatePositively
                then {
                  val argumentVariables = freshArgumentVariables(candidate.hoVar.ty, "u")
                  Substitution(hoVar, Abs.Block(argumentVariables, TopC()))
                } else if allCandidateOccuringClausesContainCandidateNegatively
                then {
                  val argumentVariables = freshArgumentVariables(candidate.hoVar.ty, "u")
                  Substitution(hoVar, Abs.Block(argumentVariables, BottomC()))
                } else {
                  Substitution(hoVar, resWitness(candidate))
                }

              wits.compose(witExtension)
            }
        }
        case Nil => Substitution(quantifiedVariables.map {
            case v @ Var(_, FunctionType(To, args)) =>
              (v, Abs.Block(rename.awayFrom(Iterable.empty).freshStream("u").take(args.size).map(FOLVar(_)), BottomC()))
          }.toMap)
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

  def resWitness(candidate: ResolutionCandidate): Expr = {
    val (abstractedResolutionCandidate, vars) = candidate.abstracted
    val resCandidate = eliminateConstraints(abstractedResolutionCandidate.clause, vars.toSet).map { case a: Atom => a }

    val resolventSet = saturateWithResolutionCandidate(abstractedResolutionCandidate, Set(HOLClause(Seq((abstractedResolutionCandidate.atom, !abstractedResolutionCandidate.index.polarity)))), Set.empty)

    val formula: Formula = abstractedResolutionCandidate.index.polarity match
      case Polarity(false) => And(resolventSet.map {
          clause => All.Block((freeFOLVariables(clause.toFormula) -- vars).toSeq, clause.toDisjunction)
        })
      case Polarity(true) => Or(resolventSet.map {
          clause => Ex.Block((freeFOLVariables(clause.toFormula) -- vars).toSeq, clause.toNegConjunction)
        })

    Abs(vars, formula)
  }

  case class Derivation(initialClauseSet: Set[HOLClause], inferences: List[Inference]):
    def tail: Derivation = inferences match
      case head :: next => {
        val (added, removed) = head(initialClauseSet)
        Derivation(initialClauseSet ++ added -- removed, next)
      }
      case Nil => ???

  def printer = pprint.copy(additionalHandlers = additionalPrinters, defaultWidth = 150)

  def additionalPrinters: PartialFunction[Any, pprint.Tree] = {
    case clauseSet: Set[_] => pprint.Tree.Apply("ClauseSet", clauseSet.iterator.map(printer.treeify(_, true, true)))
    case Derivation(initialClauseSet, inferences) => pprint.Tree.Apply(
        "Derivation", {
          val clauseSets = inferences.scanLeft(initialClauseSet)((c, i) => {
            val (added, removed) = i(c)
            c ++ added -- removed
          })
          Iterator(printer.treeify(initialClauseSet, true, true)) ++ inferences.zip(clauseSets.tail).flatMap {
            case (inference, clauses) => Seq(
                printer.treeify(clauses, true, true),
                printer.treeify(inference, true, true)
              )
          }.iterator
        }
      )
    case rc: ResolutionCandidate => printResolutionCandidate(rc)
    case hos: Sequent[_]         => pprint.Tree.Literal(hos.toString.strip())
    case Inference.Resolution(left, right) => pprint.Tree.Apply(
        "Resolution",
        Iterator(
          pprint.Tree.KeyValue("left", printer.treeify(left, false, true)),
          pprint.Tree.KeyValue("right", printer.treeify(right, false, true)),
          pprint.Tree.KeyValue("resolvent", printer.treeify(scan.resolve(left, right), false, true))
        )
      )
    case Inference.Purification(_, candidate) => pprint.Tree.Apply("Purification", Iterator(additionalPrinters(candidate)))
    case Inference.ConstraintElimination(clause, index, _) => pprint.Tree.Apply(
        "ConstraintElimination",
        Iterator(pprint.Tree.KeyValue("clause", pprint.Tree.Literal(clause.toString)), pprint.Tree.KeyValue("constraint", pprint.Tree.Literal(clause(index).toString)))
      )
    case f @ Inference.Factoring(clause, leftIndex, rightIndex) => pprint.Tree.Apply(
        "Factoring",
        Iterator(
          pprint.Tree.KeyValue("left", printer.treeify(clause(leftIndex), false, true)),
          pprint.Tree.KeyValue("right", printer.treeify(clause(rightIndex), false, true)),
          pprint.Tree.KeyValue("factor", printer.treeify(scan.factor(f), false, true))
        )
      )
  }

  def printResolutionCandidate(resolutionCandidate: ResolutionCandidate): pprint.Tree = {
    def underlineIndex(atom: Atom, index: SequentIndex) = (atom, index) match {
      case (a, i) if i == resolutionCandidate.index => s"{${a.toUntypedString}}"
      case (a, i)                                   => a.toUntypedString
    }
    val antecedentStrings = resolutionCandidate.clause.zipWithIndex.antecedent.map(underlineIndex)
    val succeedentStrings = resolutionCandidate.clause.zipWithIndex.succedent.map(underlineIndex)
    val clauseString = antecedentStrings.mkString(", ") ++ " ⊢ " ++ succeedentStrings.mkString(", ")
    pprint.Tree.Literal(clauseString.strip())
  }

  def printResult(input: FormulaEquationClauseSet, derivationLimit: Option[Int] = Some(100)) = {
    scan(input, derivationLimit) match {
      case Left(value) => {
        printer.pprintln(value, height = derivationLimit.get * 100)
        println(s"\n ❌ attempt resulted in derivation of length > ${derivationLimit.get}")
      }
      case Right(value @ (clauseSet, witnesses, derivation)) => {
        printer.pprintln(value)
        val substitutedInput = witnesses(input.clauses).map(clause => BetaReduction.betaNormalize(clause.toFormula))
        val leftFormula = And(substitutedInput)
        val rightFormula = And(clauseSet.map(_.toFormula))
        val equivalence = Iff(All.Block(freeFOLVariables(leftFormula).toSeq, leftFormula), All.Block(freeFOLVariables(rightFormula).toSeq, rightFormula))
        println("\nchecking equivalence between")
        printer.pprintln(input)
        println("with substitution")
        printer.pprintln(witnesses)
        println("and")
        printer.pprintln(clauseSet)
        println("")
        if Escargot.isValid(equivalence)
        then println(" ✅ equivalence holds")
        else println(" ❌ equivalence does NOT hold ")
      }
    }
  }
}
