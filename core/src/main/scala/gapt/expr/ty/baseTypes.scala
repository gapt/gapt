package gapt.expr.ty

object baseTypes {

  /**
   * Retrieves the base types occurring an a type.
   *
   * @param t The type whose base types are to be computed.
   * @return The set of base types occurring in type `t`.
   */
  def apply( t: Ty ): Set[TBase] = t match {
    case TArr( a, b )       => apply( a ) union apply( b )
    case t @ TBase( _, ps ) => ps.view.flatMap( apply ).toSet + t
    case TVar( _ )          => Set()
  }
}
