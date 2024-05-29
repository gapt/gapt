package gapt.expr.ty

import gapt.expr.Expr

object arity {

  /**
   * Retrieves the arity of the given type.
   *
   * @param t The type whose arity is to be computed.
   * @return The arity of the functions represented by this type.
   */
  def apply(t: Ty): Int = t match {
    case t1 ->: t2 => 1 + arity(t2)
    case _         => 0
  }

  /**
   * Retrieves the expression's arity.
   *
   * @param e The expression whose arity is to be computed.
   * @return The arity of the given expression, that is, the arity of the
   * expression's type.
   */
  def apply(e: Expr): Int = arity(e.ty)
}
