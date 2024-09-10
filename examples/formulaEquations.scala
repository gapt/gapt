package gapt.examples

import gapt.expr._
import gapt.proofs._
import gapt.logic.hol.scan.scan._

object formulaEquations {
  private def feq(vars: Set[Var], clauses: Set[HOLClause]) = {
    FormulaEquationClauseSet(vars, clauses)
  }

  def quantifiedVariableNotOccurring = feq(
    Set(hov"X:i>o"),
    Set(hcl":- A(u)")
  )

  def negationOfLeibnizEquality = feq(
    Set(hov"X:i>o"),
    Set(
      hcl"X(a), X(b) :-",
      hcl":- X(a), X(b)"
    )
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
}
