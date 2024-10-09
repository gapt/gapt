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

@main def main = {
  printWitnesses(example2, tries = 100)
}

private def feq(vars: Set[Var], clauses: Set[HOLClause]) = {
  FormulaEquationClauseSet(vars, clauses)
}

def quantifiedVariableNotOccurring = feq(Set(hov"X:i>o"), Set(hcl":- A(u)"))
def variablesAsConstants = feq(Set.empty, Set(hcl":- X(u)"))

def exampleWithPolarity = feq(
  Set(hov"X:i>o"),
  Set(hcl"A(u) :- X(u)", hcl"B(u,v), X(u) :- X(v)")
)

def negationOfLeibnizEquality = feq(
  Set(hov"X:i>o"),
  Set(hcl"X(a), X(b) :-", hcl":- X(a), X(b)")
)

def resolutionOnNonBaseLiterals = feq(
  Set(hov"X:i>o"),
  Set(
    hcl":- B(u,v)",
    hcl"B(u,v), X(u) :- X(v)",
    hcl"A(u) :- X(u)",
    hcl"X(u) :- C(u)"
  )
)

def example = feq(
  Set(hov"X:i>o"),
  Set(
    hcl"B(v) :- X(v)",
    hcl"X(u) :- A(u)"
  )
)

def example2 = feq(
  Set(hov"X:i>o"),
  Set(
    hcl"B(v) :- X(v)",
    hcl"X(u) :- A(u)",
    hcl"C(u) :- X(u)"
  )
)

def simpleDisjunction = feq(Set(hov"X:i>o"), Set(hcl":- X(a), X(b)"))
def tripleDisjunction = feq(Set(hov"X:i>o"), Set(hcl":- X(a), X(b), X(c)"))

def twoVariableExample = feq(
  Set(hov"X:i>o", hov"Y:i>i>o"),
  Set(
    hcl":- Y(a,b)",
    hcl"Y(u,u) :- X(u)",
    hcl"Y(u,v) :- Y(v,u)",
    hcl"X(a) :-"
  )
)

def exampleRequiringTautologyDeletion = feq(
  Set(hov"X:i>o"),
  Set(hcl"A(u) :- X(u)", hcl"X(u) :- X(v), A(u)", hcl"X(u) :- B(u)")
)

def exampleRequiringSubsumption = feq(
  Set(hov"X:i>o"),
  Set(
    hcl"A(u), B(u,v) :-",
    hcl"A(u) :- X(u)",
    hcl"B(u,v), X(u) :- X(v)",
    hcl"X(u) :- C(u)"
  )
)

def exampleWithSymmetryRequiringSubsumption = feq(
  Set(hov"Y:i>i>o"),
  Set(
    hcl"A(u,v), B(u,v) :-",
    hcl"A(u,v) :- Y(u,v)",
    hcl"B(u,v), Y(u,v) :- Y(v,u)",
    hcl"Y(u,v) :- C(u,v)"
  )
)

def modalCorrespondenceReflexivity = feq(
  Set(hov"X:i>o"),
  Set(
    hcl"R(a,v) :- X(v)",
    hcl"X(a) :-"
  )
)

def modalCorrespondenceTransitivity = feq(
  Set(hov"X:i>o"),
  Set(
    hcl"R(a,v) :- X(v)",
    hcl":- R(a,b)",
    hcl":- R(b,c)",
    hcl"X(c) :-"
  )
)

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
}

def printWitnesses(input: FormulaEquationClauseSet, derivationLimit: Option[Int] = Some(100), tries: Int = 10) = {
  val witnesses = scan(input, derivationLimit).take(tries).collect { case Right(_, Some(wit), _) => wit }.toSet.toSeq
  val initialEquivalenceClasses = Map.from(witnesses.map(w => (w, Set(w))))
  val nonEquivalentWitnesses = witnesses.combinations(2)
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
    }.keySet

  println("\nfound witnesses: ")
  printer.pprintln(nonEquivalentWitnesses)
}

def areEquivalent(left: Substitution, right: Substitution): Boolean = {
  left.domain.forall(v => {
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
    val substitutedInput = witnesses.get(input.clauses).map(clause => BetaReduction.betaNormalize(clause.toFormula))
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
    val result = Escargot.isValid(equivalence)
    if result
    then println(" ✅ equivalence holds")
    else println(" ❌ equivalence does NOT hold")
    result
  }
}
