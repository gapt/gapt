package gapt.examples

import gapt.expr._
import gapt.proofs._
import gapt.logic.hol.scan.scan._
import gapt.expr.formula.Formula
import gapt.expr.formula.And
import gapt.proofs.resolution.structuralCNF
import gapt.expr.formula.Atom
import gapt.expr.ty.Ti
import gapt.expr.ty.To
import gapt.logic.hol.scan.scan
import gapt.expr.util.constants
import gapt.expr.util.rename
import gapt.expr.util.freeVariables

object formulaEquations {
  private def feq(vars: Set[Var], clauses: Set[HOLClause]) = {
    FormulaEquationClauseSet(vars, clauses)
  }

  def quantifiedVariableNotOccurring = feq(Set(hov"X:i>o"), Set(hcl":- A(u)"))
  def variablesAsConstants = feq(Set.empty, Set(hcl":- X(u)"))

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

  def terminatingDerivationWhichRequiresRedundancyInWitnessConstruction = feq(
    Set(hov"X:i>o"),
    Set(hcl"A(u) :- X(u)", hcl"X(u) :- X(v), A(u)", hcl"X(u) :- B(u)")
  )

  def subsumptionBasedRedundancyWithInfiniteWitness = feq(
    Set(hov"X:i>o"),
    Set(
      hcl"A(u), B(u,v) :-",
      hcl"A(u) :- X(u)",
      hcl"B(u,v), X(u) :- X(v)",
      hcl"X(u) :- C(u)"
    )
  )

  def subsumptionBasedRedundancyWithInfiniteWitness2 = feq(
    Set(hov"X:i>o"),
    Set(
      hcl"A(u), B(u,v) :-",
      hcl"A(u) :- X(u)",
      hcl"B(u,v), X(u) :- X(v)",
      hcl"A(u) :- C(u)",
      hcl"X(u) :- C(u)"
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
}
