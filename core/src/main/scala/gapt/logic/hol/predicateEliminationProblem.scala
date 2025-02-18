package gapt.logic.hol

import gapt.expr.formula.Formula
import gapt.expr.Var
import gapt.expr.formula.Ex
import gapt.proofs.HOLClause
import gapt.expr.formula.And
import gapt.expr.formula.All
import gapt.proofs.RichFormulaSequent
import gapt.expr.Expr
import gapt.expr.formula.fol.FOLVar
import gapt.expr.util.freeVariables
import gapt.expr.formula.hol.freeHOVariables
import gapt.expr.subst.Substitution
import gapt.expr.Const
import gapt.proofs.Sequent
import gapt.proofs.resolution.structuralCNF
import gapt.expr.formula.Atom
import gapt.logic.Polarity
import gapt.proofs.lk.transformations.folSkolemize

extension (clauseSet: Set[HOLClause])
  def toFormula: Formula = {
    val quantifierFreePart = And(clauseSet.map(_.toFormula))
    All.Block(freeFOLVariables(quantifierFreePart).toSeq, quantifierFreePart)
  }

def freeFOLVariables(expr: Expr): Set[FOLVar] =
  (freeVariables(expr) -- freeHOVariables(expr)).map { case v: FOLVar => v }

case class PredicateEliminationProblem(variablesToEliminate: Set[Var], formula: Formula):
  def toFormula: Formula = Ex.Block(variablesToEliminate.toSeq, formula)
  def toClauseSet: ClauseSetPredicateEliminationProblem =
    ClauseSetPredicateEliminationProblem(variablesToEliminate, CNFp(folSkolemize(formula, Polarity.InAntecedent)))

case class ClauseSetPredicateEliminationProblem(variablesToEliminate: Set[Var], clauses: Set[HOLClause]):
  def toFormula: Formula = PredicateEliminationProblem(variablesToEliminate, clauses.toFormula).toFormula
