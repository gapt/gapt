package gapt.examples.predicateEliminationProblems

import gapt.expr._
import gapt.proofs._
import gapt.expr.ty._
import gapt.logic.hol.scan
import gapt.logic.hol.scan._
import gapt.logic.hol.wscan
import gapt.expr.util.rename
import gapt.expr.subst.Substitution
import gapt.expr.formula._
import gapt.provers.escargot.Escargot
import gapt.logic.hol.ClauseSetPredicateEliminationProblem
import gapt.logic.hol.toFormula
import gapt.logic.hol.PredicateEliminationProblem
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.fol.FOLConst
import gapt.expr.formula.fol.FOLVar
import gapt.utils.runProcess
import gapt.logic.Polarity
import gapt.utils.withTimeout

val negationOfModalAxiom = pep"?X -(!u (!v (R(u,v) -> ((!w (R(v, w) -> X(w))) <-> X(v)))))"
val exampleWithQuantifiedVariableNotOccurring = clspep"?(X:i>o) !u A(u)"
val exampleWithoutQuantifiedVariables = clspep"!u X(u)"
val exampleThatCanBeSolvedByPolarityRuleImmediately = clspep"?X(${
    Set(hcl"A(u) :- X(u)", hcl"B(u,v), X(u) :- X(v)").toFormula
  })"
val negationOfLeibnizEquality = pep"?X?u?v -(X(u) <-> X(v))"

val exampleThatUsesResolutionOnLiteralsThatAreNotQuantifiedVariables = clspep"?X(${
    Set(
      hcl":- B(u,v)",
      hcl"B(u,v), X(u) :- X(v)",
      hcl"A(u) :- X(u)",
      hcl"X(u) :- C(u)"
    ).toFormula
  })"

val exampleWithTwoClauses = clspep"?X(${
    Set(
      hcl"B(v) :- X(v)",
      hcl"X(u) :- A(u)"
    ).toFormula
  })"

val exampleWithThreeClauses = clspep"?X(${
    Set(hcl"B(v) :- X(v)", hcl"X(u) :- A(u)", hcl"C(u) :- X(u)").toFormula
  })"

val single2PartDisjunction = clspep"?X(X(a) | X(b))"
val single3PartDisjunction = clspep"?X(X(a) | X(b) | X(c))"

val exampleWithTwoVariables = clspep"?X?Y(${
    Set(
      hcl":- Y(a,b)",
      hcl"Y(u,u) :- X(u)",
      hcl"Y(u,v) :- Y(v,u)",
      hcl"X(a) :-"
    ).toFormula
  })"

val exampleRequiringTautologyDeletion = clspep"?X(${
    Set(hcl"A(u) :- X(u)", hcl"X(u) :- X(v), A(u)", hcl"X(u) :- B(u)").toFormula
  })"

val exampleRequiringSubsumption = clspep"?X(${
    Set(
      hcl"A(u), B(u,v) :-",
      hcl"A(u) :- X(u)",
      hcl"B(u,v), X(u) :- X(v)",
      hcl"X(u) :- C(u)"
    ).toFormula
  })"

val exampleWithSymmetryRequiringSubsumption = clspep"?Y(${
    Set(
      hcl"A(u,v), B(u,v) :-",
      hcl"A(u,v) :- Y(u,v)",
      hcl"B(u,v), Y(u,v) :- Y(v,u)",
      hcl"Y(u,v) :- C(u,v)"
    ).toFormula
  })"

val soqeBookDLSStarExample = clspep"?X(${
    Set(
      hcl"X(y) :- X(x), R(x,y)",
      hcl":- X(x), X(y), S(x,y)"
    ).toFormula
  })"

val unsatisfiableExampleThatRequiresFactoring = clspep"?(X:i>o)(${
    Set(
      hcl":- X(u), X(f(u))",
      hcl"X(u) :- X(f(v))",
      hcl"X(u), X(f(u)) :-"
    ).toFormula
  })"

val witnessBlowup = clspep"?X(${
    Set(
      hcl"X(c) :- ",
      hcl":- X(a_1), X(b_1)",
      hcl":- X(a_2), X(b_2)"
    ).toFormula
  })"

val twoStepRedundancy = clspep"?X(${
    Set(
      hcl"B(a, v), B(v, w) :-",
      hcl":- X(a)",
      hcl"B(u,v), X(u) :- X(v)",
      hcl"X(c) :-"
    ).toFormula
  })"

val subsumptionByXLiteral = clspep"?X(${
    Set(
      hcl":- X(a,a)",
      hcl"X(u,v) :- X(v,u), B(u,v)",
      hcl"X(b,b) :- X(c,c)",
      hcl"X(d,d) :-"
    ).toFormula
  })"

val badExample = clspep"?X(${
    Set(
      hcl":- B(b,v)",
      hcl":- B(c,v)",
      hcl"X(a) :-",
      hcl":- X(b), X(c)",
      hcl"X(u) :- B(u,v), X(v)"
    ).toFormula
  })"

val booleanUnification = pep"?X?Y((!x (#c(Pat:i>o)(x) & ?y (#c(f:i>i>o)(x,y) & X(y) & ?z (#c(s:i>i>o)(x,z) & #c(Severe:i>o)(z))))) <-> (!x (#c(Pat:i>o)(x) & ?y (#c(f:i>i>o)(x,y) & Y(y) & #c(Inj:i>o)(y) & ?z ((#c(f:i>i>o)(x,z) & #c(Head:i>o)(z)))))))"

val onlyOneSidedClauses = clspep"?X(${
    Set(
      hcl":- X(u), X(v), R(u,v)",
      hcl"X(u), X(v) :- Q(u,v)"
    ).toFormula
  })"

val wernhardUnificationExample = clspep"?X_1?X_2(!u (A(u) -> B(u)) & (!u (X_1(u) -> X_2(u)) & !u (A(u) -> X_2(u)) & !u (X_2(u) -> B(u))))"

object modalCorrespondence {
  def negationOfSecondOrderTranslationOfTAxiom = clspep"?X(${
      Set(
        hcl"R(a,v) :- X(v)",
        hcl"X(a) :-"
      ).toFormula
    })"

  def negationOfSecondOrderTranslationOf4Axiom = clspep"?X(${
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
    val inductionVar = rename.awayFrom(containedNames(theorem)).fresh(hov"X:i>o")
    Ex(
      inductionVar,
      Imp(And(additionDefinition, ind(inductionVar)), theorem)
    )
}

object graphReachability {

  def const(node: Int): FOLConst = FOLConst(s"a_$node")

  def edge(from: Int, to: Int): Atom = foa"E(${const(from)}, ${const(to)})"

  def existsPath(from: Int, to: Int, length: Int): FOLFormula = {
    require(length >= 0)
    def pathFrom(from: FOLVar | FOLConst, l: Int): FOLFormula = l match {
      case 0 => Eq(from, const(to))
      case n => {
        val v = FOLVar(s"v_$n")
        fof"?$v (E($from, $v) & ${pathFrom(v, l - 1)})"
      }
    }

    pathFrom(const(from), length)
  }

  def graph(size: Int, edges: (Int, Int)*): Set[HOLClause] = {
    require(size >= 0, "size of graph must be non-negative")
    for (from, to) <- edges do
      require(1 <= from && from <= size, s"edge ($from, $to) starting point is not in range [1, $size]")
      require(1 <= to && to <= size, s"edge ($from, $to) end point is not in range [1, $size]")

    val constants = (1 to size).map(i => Const(s"a_$i", Ti))
    def a(i: Int): Const = constants(i - 1)

    val exhaustiveness = HOLClause(Iterable.empty, constants.map(c => Eq(c, fov"u")))
    val distinctness =
      for
        i <- 1 to size
        j <- 1 until i
      yield HOLClause(Seq(Eq(a(i), a(j))), Iterable.empty)
    val edgesAndNonEdges =
      for
        i <- 1 to size
        j <- 1 to size
      yield
        val polarity = Polarity(edges.contains((i, j)))
        HOLClause(Seq((Atom(le"E:i>i>o", a(i), a(j)), polarity)))

    (distinctness ++ edgesAndNonEdges :+ exhaustiveness).toSet
  }

  def apply(size: Int, mustContain: Int, mustAvoid: Int, edges: (Int, Int)*): ClauseSetPredicateEliminationProblem = {
    val constants = (1 to size).map(i => Const(s"a_$i", Ti))
    def a(i: Int): Const = constants(i - 1)

    val graphTheory = graph(size, edges*)
    val contain = hcl":- X(${a(mustContain)})"
    val avoid = hcl"X(${a(mustAvoid)}) :-"
    val edgeClosure = hcl"X(u), E(u,v) :- X(v)"

    ClauseSetPredicateEliminationProblem(
      Seq(hov"X:i>o"),
      graphTheory + contain + avoid + edgeClosure
    )
  }
}

def exportToScan(varsToEliminate: Seq[Var], clauses: Seq[HOLClause]): String = {
  val predList = varsToEliminate.map(v => v.name).mkString(", ")
  val cls = clauses.map { clause =>
    val foVariables = freeFOLVariables(clause.toFormula)
    def atomToScan(a: Atom): String = a match {
      case Eq(left, right) => s"$left=$right"
      case a               => a.toUntypedAsciiString
    }
    val negativeLiterals = clause.antecedent.map(atomToScan).map(a => s"-($a)")
    val positiveLiterals = clause.succedent.map(atomToScan)
    val quantifierFreePart = s"(${(negativeLiterals ++ positiveLiterals).mkString(" | ")})"
    if foVariables.isEmpty then {
      s"$quantifierFreePart."
    } else {
      s"all ${foVariables.toSeq.mkString(" ")} $quantifierFreePart."
    }
  }
  s"""
  pred_list[$predList].
  %set(unskolemize).
  %set(negate).
  ;.
  set(binary_res).
  set(for_sub).
  set(back_sub).
  set(very_verbose).
  assign(max_seconds, 5).

  % 1.assign(check_redundancy_time,s).
  % try to prove each generated clause in s seconds from rest
  % of clause set minus pure clause. Drop clause if it can be proven.
  % No redundancy check if s = 0.
  assign(check_redundancy_time, 0).

  % 2.assign(minimize_at_end_time,s).
  % after Scan has finished, try to prove each remaining
  % clause from the other clauses in s seconds, starting with long clauses.
  % Drop clause if it can be proven. No minimization if s = 0
  assign(minimize_at_end_time,0).

  %% comments on the search
  %%clear(very_verbose).
  %clear(print_kept).
  %clear(print_given).
  %clear(print_back_sub).
  %%
  %clear(print_new_demod).
  %clear(print_back_demod).
  %clear(print_proofs).

  set(print_lists_at_end).

  %formula_list(usable).
  %end_of_list.

  formula_list(sos).

  ${cls.mkString("\n")}

  end_of_list.
  """.stripMargin
}

def runScan(varsToEliminate: Seq[Var], clauses: Seq[HOLClause]): Int = {
  import scala.concurrent._
  import scala.concurrent.duration._
  import scala.io._
  val scanInput = exportToScan(varsToEliminate, clauses)
  val (exitValue, stdout) =
    runProcess.withExitValue(Seq("docker", "run", "-i", "scan-app"), stdin = scanInput)
  println(stdout)
  if exitValue == 127 then
    println("exit value is 127. is docker running?")
  exitValue
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
        val clauseSets = inferences.scanLeft(initialClauseSet)((c, i) =>
          ClauseSetPredicateEliminationProblem(c.varsToEliminate, i(c.firstOrderClauses))
        )
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
  val clauseString = (antecedentStrings.mkString(", ") ++ Seq("⊢") ++ succeedentStrings.mkString(", ")).mkString(" ")
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

def isWSOQEWitness(input: PredicateEliminationProblem, firstOrderEquivalent: FOLFormula, witness: Substitution): Boolean =
  witness.domain == input.varsToEliminate.toSet &&
    Escargot.isValid(Iff(firstOrderEquivalent, BetaReduction.betaNormalize(witness(input.firstOrderPart))))

def inputSize(clauseSet: ClauseSetPredicateEliminationProblem): Int =
  clauseSet.firstOrderClauses.toSeq.map(c => c.elements.map(numberOfSymbols).sum).sum

def numberOfSymbols(expr: Expr): Int = expr match {
  case _: VarOrConst => 1
  case App(f, args)  => numberOfSymbols(f) + numberOfSymbols(args)
  case Abs(_, inner) => numberOfSymbols(inner)
}

def witnessSize(substitution: Substitution): Int =
  substitution.map.values.toSeq.map(numberOfSymbols).sum

def wscanTestExample(example: ClauseSetPredicateEliminationProblem) =
  val exampleSize = inputSize(example)
  println(s"Testing example ${example}")
  val startTime = java.lang.System.nanoTime()
  val witness = wscan(example)
  val durationInNanoSeconds = java.lang.System.nanoTime() - startTime
  val result = (witness, durationInNanoSeconds, exampleSize, witness.map(witnessSize))
  println(s"Got result ${result}")
  result

def wscanTest() =
  val examples: List[ClauseSetPredicateEliminationProblem] = List(
    negationOfModalAxiom.toClauseSet,
    exampleWithQuantifiedVariableNotOccurring,
    exampleWithoutQuantifiedVariables,
    exampleThatCanBeSolvedByPolarityRuleImmediately,
    negationOfLeibnizEquality.toClauseSet,
    exampleThatUsesResolutionOnLiteralsThatAreNotQuantifiedVariables,
    exampleWithTwoClauses,
    exampleWithThreeClauses,
    single2PartDisjunction,
    single3PartDisjunction,
    exampleWithTwoVariables,
    exampleRequiringTautologyDeletion,
    exampleRequiringSubsumption,
    exampleWithSymmetryRequiringSubsumption,
    soqeBookDLSStarExample,
    unsatisfiableExampleThatRequiresFactoring,
    witnessBlowup,
    twoStepRedundancy,
    subsumptionByXLiteral,
    badExample,
    booleanUnification.toClauseSet,
    onlyOneSidedClauses,
    wernhardUnificationExample,
    graphReachability(3, 0, 2, 0 -> 1),
    modalCorrespondence.negationOfSecondOrderTranslationOfTAxiom,
    modalCorrespondence.negationOfSecondOrderTranslationOf4Axiom
  )
  println(s"Testing ${examples.size} examples")

  val results = examples.map(wscanTestExample)

  val resultsWithWitnesses = results
    .filter((wit, _, _, _) => wit.isDefined)
    .map((wit, d, i, s) => (wit.get, d, i, s.get))
  val foundWitnesses = resultsWithWitnesses.size
  val successPercentage = (foundWitnesses.toDouble / results.size) * 100.0

  println(s"Tested ${examples.size} examples")
  println(f"For ${foundWitnesses} a witness could be found ($successPercentage%.2f%%)")

  val minExampleSize = results.minBy(_._3)._3
  val maxExampleSize = results.maxBy(_._3)._3
  val averageExampleSize = results.map(_._3).sum.toDouble / results.size

  println(s"min example size: $minExampleSize")
  println(s"max example size: $maxExampleSize")
  println(f"avg example size: $averageExampleSize%.2f")

  val minSuccessfulDuration = resultsWithWitnesses.minBy(_._2)._2 / 1000000.0
  val maxSuccessfulDuration = resultsWithWitnesses.maxBy(_._2)._2 / 1000000.0
  val averageSuccessfulDuration = resultsWithWitnesses.map(_._2).sum.toDouble / (1000000.0 * results.size)

  println(f"min successful duration: $minSuccessfulDuration%.2f ms")
  println(f"max successful duration: $maxSuccessfulDuration%.2f ms")
  println(f"avg successful duration: $averageSuccessfulDuration%.2f ms")

  val minWitnessSize = resultsWithWitnesses.minBy(_._4)._4
  val maxWitnessSize = resultsWithWitnesses.maxBy(_._4)._4
  val averageWitnessSize = resultsWithWitnesses.map(_._4).sum.toDouble / results.size

  println(s"min witness size: $minWitnessSize")
  println(s"max witness size: $maxWitnessSize")
  println(f"avg witness size: $averageWitnessSize%.2f")

  println("Finished run")
