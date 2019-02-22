package gapt.expr.formula.fol

import gapt.expr.Expr

private[expr] trait FOLPartialFormula extends Expr {
  private[expr] def numberOfArguments: Int
}
