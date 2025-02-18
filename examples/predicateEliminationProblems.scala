package gapt.examples.predicateEliminationProblems

import gapt.expr._
import gapt.proofs._
import gapt.proofs.resolution.structuralCNF
import gapt.expr.ty.Ti
import gapt.expr.ty.To
import gapt.logic.hol.scan
import gapt.logic.hol.scan._
import gapt.logic.hol.wscan
import gapt.expr.util.constants
import gapt.expr.util.rename
import gapt.expr.util.freeVariables
import gapt.expr.subst.Substitution
import gapt.expr.formula._
import gapt.provers.escargot.Escargot
import gapt.logic.hol.dls.dls
import scala.util.Success
import gapt.expr.formula.hol.freeHOVariables
import gapt.logic.hol.ClauseSetPredicateEliminationProblem
import gapt.logic.hol.toFormula
import gapt.logic.hol.skolemize
import gapt.logic.Polarity
import gapt.logic.hol.CNFp
import gapt.proofs.lk.transformations.folSkolemize
import gapt.logic.hol.PredicateEliminationProblem

@main def main = {
  printResultInteractive(wernhardUnificationExample.toClauseSet)
}

val negationOfModalAxiom = pep"?X -(!u (!v (R(u,v) -> ((!w (R(v, w) -> X(w))) <-> X(v)))))"

def scanOneByOne(vars: Seq[Var], clauses: Set[HOLClause]): Option[Seq[(Set[HOLClause], Option[Substitution], Derivation)]] = {
  vars.foldLeft[Option[Seq[(Set[HOLClause], Option[Substitution], Derivation)]]](Some(Seq((clauses, Some(Substitution()), Derivation(clauses, List.empty))))) {
    case (None, v) => None
    case (Some(state), v) => {
      for (derivation, wit) <- wscan(ClauseSetPredicateEliminationProblem(Set(v), state.last._1)).take(10).collect {
          case Right(result) => result
        }.nextOption()
      yield state :+ (derivation.conclusion, wit, derivation)
    }
  }
}

val exampleWithQuantifiedVariableNotOccurring = pep"?(X:i>o) !u A(u)"
val exampleWithoutQuantifiedVariables = pep"!u X(u)"
val exampleThatCanBeSolvedByPolarityRuleImmediately = pep"?X(${
    Set(hcl"A(u) :- X(u)", hcl"B(u,v), X(u) :- X(v)").toFormula
  })"
val negationOfLeibnizEquality = pep"?X?u?v -(X(u) <-> X(v))"

val exampleThatUsesResolutionOnLiteralsThatAreNotQuantifiedVariables = pep"?X(${
    Set(
      hcl":- B(u,v)",
      hcl"B(u,v), X(u) :- X(v)",
      hcl"A(u) :- X(u)",
      hcl"X(u) :- C(u)"
    ).toFormula
  })"

val exampleWithTwoClauses = pep"?X(${
    Set(
      hcl"B(v) :- X(v)",
      hcl"X(u) :- A(u)"
    ).toFormula
  })"

val exampleWithThreeClauses = pep"?X(${
    Set(hcl"B(v) :- X(v)", hcl"X(u) :- A(u)", hcl"C(u) :- X(u)").toFormula
  })"

val single2PartDisjunction = pep"?X(X(a) | X(b))"
val single3PartDisjunction = pep"?X(X(a) | X(b) | X(c))"

val exampleWithTwoVariables = pep"?X?Y(${
    Set(
      hcl":- Y(a,b)",
      hcl"Y(u,u) :- X(u)",
      hcl"Y(u,v) :- Y(v,u)",
      hcl"X(a) :-"
    ).toFormula
  })"

val exampleRequiringTautologyDeletion = pep"?X(${
    Set(hcl"A(u) :- X(u)", hcl"X(u) :- X(v), A(u)", hcl"X(u) :- B(u)").toFormula
  })"

val exampleRequiringSubsumption = pep"?X(${
    Set(
      hcl"A(u), B(u,v) :-",
      hcl"A(u) :- X(u)",
      hcl"B(u,v), X(u) :- X(v)",
      hcl"X(u) :- C(u)"
    ).toFormula
  })"

val exampleWithSymmetryRequiringSubsumption = pep"?Y(${
    Set(
      hcl"A(u,v), B(u,v) :-",
      hcl"A(u,v) :- Y(u,v)",
      hcl"B(u,v), Y(u,v) :- Y(v,u)",
      hcl"Y(u,v) :- C(u,v)"
    ).toFormula
  })"

val soqeBookDLSStarExample = pep"?X(${
    Set(
      hcl"X(y) :- X(x), R(x,y)",
      hcl":- X(x), X(y), S(x,y)"
    ).toFormula
  })"

val unsatisfiableExampleThatRequiresFactoring = pep"?(X:i>o)(${
    Set(
      hcl":- X(u), X(f(u))",
      hcl"X(u) :- X(f(v))",
      hcl"X(u), X(f(u)) :-"
    ).toFormula
  })"

val witnessBlowup = pep"?X(${
    Set(
      hcl"X(c) :- ",
      hcl":- X(a_1), X(b_1)",
      hcl":- X(a_2), X(b_2)"
    ).toFormula
  })"

val twoStepRedundancy = pep"?X(${
    Set(
      hcl"B(a, v), B(v, w) :-",
      hcl":- X(a)",
      hcl"B(u,v), X(u) :- X(v)",
      hcl"X(c) :-"
    ).toFormula
  })"

val subsumptionByXLiteral = pep"?X(${
    Set(
      hcl":- X(a,a)",
      hcl"X(u,v) :- X(v,u), B(u,v)",
      hcl"X(b,b) :- X(c,c)",
      hcl"X(d,d) :-"
    ).toFormula
  })"

val badExample = pep"?X(${
    Set(
      hcl":- B(b,v)",
      hcl":- B(c,v)",
      hcl"X(a) :-",
      hcl":- X(b), X(c)",
      hcl"X(u) :- B(u,v), X(v)"
    ).toFormula
  })"

val booleanUnification = pep"?X?Y((!x (#c(Pat:i>o)(x) & ?y (#c(f:i>i>o)(x,y) & X(y) & ?z (#c(s:i>i>o)(x,z) & #c(Severe:i>o)(z))))) <-> (!x (#c(Pat:i>o)(x) & ?y (#c(f:i>i>o)(x,y) & Y(y) & #c(Inj:i>o)(y) & ?z ((#c(f:i>i>o)(x,z) & #c(Head:i>o)(z)))))))"

val onlyOneSidedClauses = pep"?X(${
    Set(
      hcl":- X(u), X(v), R(u,v)",
      hcl"X(u), X(v) :- Q(u,v)"
    ).toFormula
  })"

val wernhardUnificationExample = pep"?X_1?X_2(!u (A(u) -> B(u)) & (!u (X_1(u) -> X_2(u)) & !u (A(u) -> X_2(u)) & !u (X_2(u) -> B(u))))"

val graphReachability = pep"?X(${
    hos":- !x (x = a_1 | x = a_2 | x = a_3) & a_1 != a_2 & a_1 != a_3 & a_2 != a_3 & E(a_1,a_2) & E(a_2,a_1) & E(a_3,a_2) & -E(a_1,a_1) & -E(a_2_,a_2) & -E(a_3,a_3) & -E(a_1,a_3) & -E(a_2,a_3) & -E(a_3,a_1) & (X(a_1) & !u!v((X(u) & E(u,v)) -> X(v)) & -X(a_3))".toFormula
  })"

object modalCorrespondence {
  def negationOfSecondOrderTranslationOfTAxiom = pep"?X(${
      Set(
        hcl"R(a,v) :- X(v)",
        hcl"X(a) :-"
      ).toFormula
    })"

  def negationOfSecondOrderTranslationOf4Axiom = pep"?X(${
      Set(
        hcl"R(a,v) :- X(v)",
        hcl":- R(a,b)",
        hcl":- R(b,c)",
        hcl"X(c) :-"
      ).toFormula
    })"
}

object induction {
  def additionDefinition = And(Set(
    fof"!u u + 0 = u",
    fof"!u !v u + s(v) = s(u+v)"
  ))

  def ind(expr: Expr): Formula = {
    assert(expr.ty == Ti ->: To)
    BetaReduction.betaNormalize(hof"($expr(0) & !u ($expr(u) -> $expr(s(u)))) -> !u $expr(u)")
  }

  def inductiveTheorem(theorem: Formula) =
    pep"?X (($additionDefinition) & (${ind(hov"X:i>o")}) -> $theorem)"
}

def printer = pprint.copy(additionalHandlers = additionalPrinters, defaultWidth = 150)

def additionalPrinters: PartialFunction[Any, pprint.Tree] = {
  case clauseSet: Set[_] =>
    pprint.Tree.Apply(
      "Set",
      clauseSet.iterator.map(printer.treeify(_, true, true))
    )
  case Derivation(initialClauseSet, inferences) => pprint.Tree.Apply(
      "Derivation", {
        val clauseSets = inferences.scanLeft(initialClauseSet)((c, i) => i(c))
        Iterator(printer.treeify(initialClauseSet, true, true)) ++ inferences.zip(clauseSets.tail).flatMap {
          case (inference, clauses) => Seq(
              printer.treeify(inference, true, true),
              printer.treeify(clauses, true, true)
            )
        }.iterator
      }
    )
  case rc: PointedClause => printResolutionCandidate(rc)
  case hos: Sequent[_]   => printSequent(hos)
  case DerivationStep.ConstraintResolution(left, right) => pprint.Tree.Apply(
      "Resolution",
      Iterator(
        pprint.Tree.KeyValue("left", printer.treeify(left, false, true)),
        pprint.Tree.KeyValue("right", printer.treeify(right, false, true)),
        pprint.Tree.KeyValue("resolvent", printer.treeify(constraintResolvent(left, right), false, true))
      )
    )
  case DerivationStep.PurifiedClauseDeletion(candidate) => pprint.Tree.Apply("Purification", Iterator(additionalPrinters(candidate)))
  case DerivationStep.ConstraintElimination(clause, index, _) => pprint.Tree.Apply(
      "ConstraintElimination",
      Iterator(pprint.Tree.KeyValue("clause", printer.treeify(clause, false, true)), pprint.Tree.KeyValue("constraint", printer.treeify(clause(index), false, true)))
    )
  case f @ DerivationStep.ConstraintFactoring(clause, leftIndex, rightIndex) => pprint.Tree.Apply(
      "Factoring",
      Iterator(
        pprint.Tree.KeyValue("left", printer.treeify(clause(leftIndex), false, true)),
        pprint.Tree.KeyValue("right", printer.treeify(clause(rightIndex), false, true)),
        pprint.Tree.KeyValue("factor", printer.treeify(scan.factor(f), false, true))
      )
    )
  case s: Substitution => pprint.Tree.Apply(
      "Substitution",
      s.map.map { (v, expr) =>
        pprint.Tree.Infix(printer.treeify(v, false, true), "->", printer.treeify(expr, false, true))
      }.iterator
    )
}

def printSequent[T](sequent: Sequent[T]): pprint.Tree = {
  def toStr(e: T) = e match {
    case e: Expr => e.toUntypedString
    case e       => e.toString()
  }
  val antecedentStrings = sequent.antecedent.map(toStr)
  val succeedentStrings = sequent.succedent.map(toStr)
  val clauseString = antecedentStrings.mkString(", ") ++ " ⊢ " ++ succeedentStrings.mkString(", ")
  pprint.Tree.Literal(clauseString.strip())
}

def printResolutionCandidate(resolutionCandidate: PointedClause): pprint.Tree = {
  def underlineIndex(atom: Atom, index: SequentIndex) = (atom, index) match {
    case (a, i) if i == resolutionCandidate.index => s"{${a.toUntypedString}}"
    case (a, i)                                   => a.toUntypedString
  }
  val antecedentStrings = resolutionCandidate.clause.zipWithIndex.antecedent.map(underlineIndex)
  val succeedentStrings = resolutionCandidate.clause.zipWithIndex.succedent.map(underlineIndex)
  val clauseString = antecedentStrings.mkString(", ") ++ " ⊢ " ++ succeedentStrings.mkString(", ")
  pprint.Tree.Literal(clauseString.strip())
}

def getSolutions(input: ClauseSetPredicateEliminationProblem, derivationLimit: Option[Int], possibilityLimit: Option[Int]): Iterator[(Derivation, Option[Substitution])] = {
  val baseIterator = wscan(input, derivationLimit)
  val iterator = if possibilityLimit.isDefined then baseIterator.take(possibilityLimit.get) else baseIterator
  iterator.collect { case Right(output) => output }
}

def printResult(input: ClauseSetPredicateEliminationProblem, derivationLimit: Option[Int] = Some(100), possibilityLimit: Option[Int] = Some(10)) = {
  val solutions = getSolutions(input, derivationLimit, possibilityLimit)
  if solutions.isEmpty then {
    println(s"❌ didn't find solution")
  } else solutions.foreach(checkSolution(input, _))

}

def equivalenceClasses[T](base: Iterable[T])(areEquivalent: (T, T) => Boolean): Map[T, Set[T]] = {
  val input = base.toSet
  val initialEquivalenceClasses = Map.from(input.map(w => (w, Set(w))))
  input.toSeq.combinations(2)
    .foldLeft(initialEquivalenceClasses) {
      case (classes, Seq(left, right)) => {
        val leftEquivalentToRight = areEquivalent(left, right)
        classes.updatedWith(left) {
          case Some(equivalents) if leftEquivalentToRight =>
            Some(equivalents + right)
          case s => s
        }.updatedWith(right) {
          case Some(equivalents) if leftEquivalentToRight => None
          case s                                          => s
        }
      }
    }
}

def formatPercentage(count: Int, of: Int): String =
  "%.1f%%".formatLocal(java.util.Locale.UK, (count * 100).floatValue / of)

def printWitnesses(input: ClauseSetPredicateEliminationProblem, derivationLimit: Option[Int] = Some(100), witnessLimit: Option[Int] = Some(100), tries: Int = 100) = {
  println("finding witnesses for")
  printer.pprintln(input.toFormula)
  val scanOutput = wscan(input, derivationLimit, witnessLimit).take(tries).toSeq
  val successfulScanRuns = scanOutput.collect { case Right(x) => x }
  val witnesses = successfulScanRuns.collect { case (derivation, Some(wit)) => (derivation.conclusion.toFormula, wit) }
  val runsWithoutFiniteWitnesses = successfulScanRuns.size - witnesses.size
  val nonEquivalent = equivalenceClasses(witnesses) {
    case ((_, left), (_, right)) => areEquivalent(left, right)
  }
  println(s"tried ${scanOutput.size} scan runs with derivationlimit $derivationLimit and witness limit $witnessLimit")
  println(s"${successfulScanRuns.size} (${formatPercentage(successfulScanRuns.size, scanOutput.size)}) of those succeeded")
  println(s"${witnesses.size} (${formatPercentage(witnesses.size, successfulScanRuns.size)}) of the successful ones produced a finite witness")
  println(s"${runsWithoutFiniteWitnesses} (${formatPercentage(runsWithoutFiniteWitnesses, successfulScanRuns.size)}) of the successful ones did not produce a finite witness")
  println(s"${nonEquivalent.size} (${formatPercentage(nonEquivalent.size, witnesses.size)}) of the found witnesses are mutually non-equivalent")
  println("those are: ")
  nonEquivalent.keySet.foreach(printer.pprintln(_))
}

def areEquivalent(left: Substitution, right: Substitution): Boolean = {
  left.domain == right.domain && left.domain.forall(v => {
    val vars = wscan.freshArgumentVariables(v.ty, "u")
    val leftFormula = BetaReduction.betaNormalize(App(left(v), vars)).asInstanceOf[Formula]
    val rightFormula = BetaReduction.betaNormalize(App(right(v), vars)).asInstanceOf[Formula]
    Escargot.isValid(Iff(leftFormula, rightFormula))
  })
}

def printResultInteractive(input: ClauseSetPredicateEliminationProblem, derivationLimit: Option[Int] = Some(100)) = {
  val iterator = wscan(input, derivationLimit)

  while (iterator.hasNext) {
    iterator.next() match {
      case Left(value) => {
        printer.pprintln(value, height = derivationLimit.get * 100)
        println(s"\n ❌ attempt resulted in derivation of length > ${derivationLimit.get}")
        scala.io.StdIn.readLine("press enter to show next solution: ")
        System.out.flush()
      }
      case Right(output) => {
        checkSolution(input, output)
        if iterator.hasNext then
          scala.io.StdIn.readLine("press enter to show next solution: ")
          System.out.flush()
      }
    }
  }
}

def checkSolution(input: ClauseSetPredicateEliminationProblem, output: (Derivation, Option[Substitution])): Boolean = {
  val (derivation, witness) = output
  printer.pprintln(output)
  if witness.isEmpty then {
    println("❌ could not construct a finite witness")
    false
  } else {
    checkWitness(And(input.clauses.map(_.toFormula)), derivation.conclusion.toFormula, witness.get)
  }
}

def checkWitness(input: Formula, output: Formula, witness: Substitution): Boolean = {
  val leftFormula = BetaReduction.betaNormalize(witness(input))
  val rightFormula = output
  val equivalence = Iff(All.Block(freeFOLVariables(leftFormula).toSeq, leftFormula), All.Block(freeFOLVariables(rightFormula).toSeq, rightFormula))
  println("\nchecking equivalence between")
  printer.pprintln(input)
  println("with substitution")
  printer.pprintln(witness)
  println("and")
  printer.pprintln(output)
  println("")
  val result = Escargot.isValid(equivalence)
  if result
  then println(" ✅ equivalence holds")
  else println(" ❌ equivalence does NOT hold")
  result
}
