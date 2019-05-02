package gapt.expr.formula.fol

trait FOLTerm extends FOLPartialTerm with FOLExpression {
  private[expr] override val numberOfArguments = 0
}
