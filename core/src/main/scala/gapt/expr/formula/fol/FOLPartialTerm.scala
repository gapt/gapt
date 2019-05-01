package gapt.expr.formula.fol

import gapt.expr.Expr

trait FOLPartialTerm extends Expr {
  private[expr] def numberOfArguments: Int
}
