package gapt.examples.formulaEquations

import gapt.expr._
import gapt.proofs._
import gapt.logic.hol.scan.scan._
import gapt.proofs.resolution.structuralCNF
import gapt.expr.ty.Ti
import gapt.expr.ty.To
import gapt.logic.hol.scan.scan
import gapt.expr.util.constants
import gapt.expr.util.rename
import gapt.expr.util.freeVariables
import gapt.expr.subst.Substitution
import gapt.expr.formula._
import gapt.provers.escargot.Escargot
import gapt.logic.hol.dls.dls
import scala.util.Success

@main def main = {
  printResultInteractive(insatisfiableExampleThatRequiresFactoring)
}

def scanOneByOne(vars: Seq[Var], clauses: Set[HOLClause]): Option[Seq[(Set[HOLClause], Option[Substitution], Derivation)]] = {
  vars.foldLeft[Option[Seq[(Set[HOLClause], Option[Substitution], Derivation)]]](Some(Seq((clauses, Some(Substitution()), Derivation(clauses, List.empty))))) {
    case (None, v) => None
    case (Some(state), v) => {
      for result <- scan(feq(Set(v), state.last._1)).take(10).collect {
          case Right(result) => result
        }.nextOption()
      yield state :+ result
    }
  }
}

private def feq(vars: Set[Var], clauses: Set[HOLClause]) = {
  FormulaEquationClauseSet(vars, clauses)
}

val exampleWithQuantifiedVariableNotOccurring = feq(Set(hov"X:i>o"), Set(hcl":- A(u)"))
val exampleWithoutQuantifiedVariables = feq(Set.empty, Set(hcl":- X(u)"))

val exampleThatCanBeSolvedByPolarityRuleImmediately = feq(
  Set(hov"X:i>o"),
  Set(hcl"A(u) :- X(u)", hcl"B(u,v), X(u) :- X(v)")
)

val negationOfLeibnizEquality = feq(
  Set(hov"X:i>o"),
  Set(hcl"X(a), X(b) :-", hcl":- X(a), X(b)")
)

val exampleThatUsesResolutionOnLiteralsThatAreNotQuantifiedVariables = feq(
  Set(hov"X:i>o"),
  Set(
    hcl":- B(u,v)",
    hcl"B(u,v), X(u) :- X(v)",
    hcl"A(u) :- X(u)",
    hcl"X(u) :- C(u)"
  )
)

val exampleWithTwoClauses = feq(
  Set(hov"X:i>o"),
  Set(
    hcl"B(v) :- X(v)",
    hcl"X(u) :- A(u)"
  )
)

val exampleWithThreeClauses = feq(
  Set(hov"X:i>o"),
  Set(
    hcl"B(v) :- X(v)",
    hcl"X(u) :- A(u)",
    hcl"C(u) :- X(u)"
  )
)

val single2PartDisjunction = feq(Set(hov"X:i>o"), Set(hcl":- X(a), X(b)"))
val single3PartDisjunction = feq(Set(hov"X:i>o"), Set(hcl":- X(a), X(b), X(c)"))

val exampleWithTwoVariables = feq(
  Set(hov"X:i>o", hov"Y:i>i>o"),
  Set(
    hcl":- Y(a,b)",
    hcl"Y(u,u) :- X(u)",
    hcl"Y(u,v) :- Y(v,u)",
    hcl"X(a) :-"
  )
)

val exampleRequiringTautologyDeletion = feq(
  Set(hov"X:i>o"),
  Set(hcl"A(u) :- X(u)", hcl"X(u) :- X(v), A(u)", hcl"X(u) :- B(u)")
)

val exampleRequiringSubsumption = feq(
  Set(hov"X:i>o"),
  Set(
    hcl"A(u), B(u,v) :-",
    hcl"A(u) :- X(u)",
    hcl"B(u,v), X(u) :- X(v)",
    hcl"X(u) :- C(u)"
  )
)

val exampleWithSymmetryRequiringSubsumption = feq(
  Set(hov"Y:i>i>o"),
  Set(
    hcl"A(u,v), B(u,v) :-",
    hcl"A(u,v) :- Y(u,v)",
    hcl"B(u,v), Y(u,v) :- Y(v,u)",
    hcl"Y(u,v) :- C(u,v)"
  )
)

val soqeBookDLSStarExample = feq(
  Set(hov"X:i>o"),
  Set(
    hcl"X(y) :- X(x), R(x,y)",
    hcl":- X(x), X(y), S(x,y)"
  )
)

val insatisfiableExampleThatRequiresFactoring = feq(
  Set(hov"X:i>i>o"),
  Set(
    hcl":- X(u), X(f(u))",
    hcl"X(u) :- X(f(v))",
    hcl"X(u), X(f(u)) :-"
  )
)

object modalCorrespondence {
  def negationOfSecondOrderTranslationOfTAxiom = feq(
    Set(hov"X:i>o"),
    Set(
      hcl"R(a,v) :- X(v)",
      hcl"X(a) :-"
    )
  )

  def negationOfSecondOrderTranslationOf4Axiom = feq(
    Set(hov"X:i>o"),
    Set(
      hcl"R(a,v) :- X(v)",
      hcl":- R(a,b)",
      hcl":- R(b,c)",
      hcl"X(c) :-"
    )
  )
}

object induction {
  def Q = And(Set(
    fof"!u s(u) != 0",
    fof"!u u + 0 = u",
    fof"!u !v u + s(v) = s(u+v)"
  ))

  def ind(expr: Expr): Formula = {
    assert(expr.ty == Ti ->: To)
    BetaReduction.betaNormalize(hof"($expr(0) & !u ($expr(u) -> $expr(s(u)))) -> !u $expr(u)")
  }

  def soaFree(v: Var) = {
    Q & ind(v)
  }

  def inductiveTheorem(theorem: Formula) = {
    val freshConstant = rename(hoc"P:i>o", freeVariables(theorem))
    val freshVariable = rename(hov"X:i>o", freeVariables(theorem))
    val formula = hof"($Q & ${ind(freshConstant)}) -> $theorem"
    val clauses = cnf(formula)
    val renamedClauses = clauses.map(c => {
      c.map {
        case Atom(head, args) if head == freshConstant => Atom(freshVariable, args)
        case a                                         => a
      }
    })
    feq(Set(freshVariable), renamedClauses)
  }

  def cnf(formula: Formula) = {
    val sequent = hos"$formula :-"
    structuralCNF(sequent, structural = false).map(_.conclusion.map(_.asInstanceOf[Atom]))
  }
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
        val clauseSets = inferences.scanLeft(initialClauseSet)((c, i) => {
          val (added, removed) = i(c)
          c ++ added -- removed
        })
        Iterator(printer.treeify(initialClauseSet, true, true)) ++ inferences.zip(clauseSets.tail).flatMap {
          case (inference, clauses) => Seq(
              printer.treeify(inference, true, true),
              printer.treeify(clauses, true, true)
            )
        }.iterator
      }
    )
  case rc: ResolutionCandidate => printResolutionCandidate(rc)
  case hos: Sequent[_]         => printSequent(hos)
  case Inference.Resolution(left, right) => pprint.Tree.Apply(
      "Resolution",
      Iterator(
        pprint.Tree.KeyValue("left", printer.treeify(left, false, true)),
        pprint.Tree.KeyValue("right", printer.treeify(right, false, true)),
        pprint.Tree.KeyValue("resolvent", printer.treeify(scan.resolve(left, right), false, true))
      )
    )
  case Inference.Purification(candidate) => pprint.Tree.Apply("Purification", Iterator(additionalPrinters(candidate)))
  case Inference.ConstraintElimination(clause, index, _) => pprint.Tree.Apply(
      "ConstraintElimination",
      Iterator(pprint.Tree.KeyValue("clause", printer.treeify(clause, false, true)), pprint.Tree.KeyValue("constraint", printer.treeify(clause(index), false, true)))
    )
  case f @ Inference.Factoring(clause, leftIndex, rightIndex) => pprint.Tree.Apply(
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

def printResult(input: FormulaEquationClauseSet, derivationLimit: Option[Int] = Some(100), possibilityLimit: Option[Int] = Some(10)) = {
  val baseIterator = scan(input, derivationLimit)
  val iterator = if possibilityLimit.isDefined then baseIterator.take(possibilityLimit.get) else baseIterator
  val solution = iterator.find {
    case Left(value)   => false
    case Right(output) => checkSolution(input, output)
  }

  if solution.isEmpty then {
    println(s"❌ didn't find solution")
  }
}

def nonEquivalentWitnesses(witnesses: Set[Substitution]): Map[Substitution, Set[Substitution]] = {
  val initialEquivalenceClasses = Map.from(witnesses.map(w => (w, Set(w))))
  witnesses.toSeq.combinations(2)
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

def printWitnesses(input: FormulaEquationClauseSet, derivationLimit: Option[Int] = Some(100), witnessLimit: Int = 100, tries: Int = 100) = {
  println("finding witnesses for")
  printer.pprintln(input.toFormula)
  val scanOutput = scan(input, derivationLimit, witnessLimit).take(tries).toSeq
  val successfulScanRuns = scanOutput.collect { case Right(x) => x }
  val witnesses = successfulScanRuns.collect { case (_, Some(wit), _) => wit }
  val runsWithoutFiniteWitnesses = successfulScanRuns.size - witnesses.size
  val nonEquivalent = nonEquivalentWitnesses(witnesses.toSet)
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
    val vars = freshArgumentVariables(v.ty, "u")
    val leftFormula = BetaReduction.betaNormalize(App(left(v), vars)).asInstanceOf[Formula]
    val rightFormula = BetaReduction.betaNormalize(App(right(v), vars)).asInstanceOf[Formula]
    Escargot.isValid(Iff(leftFormula, rightFormula))
  })
}

def printResultInteractive(input: FormulaEquationClauseSet, derivationLimit: Option[Int] = Some(100)) = {
  val iterator = scan(input, derivationLimit)

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

def checkSolution(input: FormulaEquationClauseSet, output: (Set[HOLClause], Option[Substitution], Derivation)): Boolean = {
  val (clauseSet, witnesses, derivation) = output
  printer.pprintln(output)
  if witnesses.isEmpty then {
    println("❌ could not construct a finite witness")
    false
  } else {
    checkWitness(And(input.clauses.map(_.toFormula)), And(clauseSet.map(_.toFormula)), witnesses.get)
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
