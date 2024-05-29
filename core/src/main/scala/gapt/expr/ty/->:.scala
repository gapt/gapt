package gapt.expr.ty

object ->: {

  /**
   * Interprets the given type as an arrow type.
   *
   * @param ty The type to be interpreted as an arrow type.
   * @return Returns Some( (t,r) ) if `ty` = t -> r, otherwise None is
   * returned.
   */
  def unapply(ty: Ty): Option[(Ty, Ty)] =
    ty match {
      case TArr(a, b) => Some((a, b))
      case _          => None
    }
}
