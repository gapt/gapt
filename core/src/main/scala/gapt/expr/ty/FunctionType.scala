package gapt.expr.ty

object FunctionType {

  /**
   * Creates a function type.
   *
   * @param to The return type of the newly created function type.
   * @param from The argument types of the newly created function type.
   * @return A type of the form
   * `from(0)` -> ( `from(1)` -> ( ... (`from(n)` -> `to`)...)),
   * where n is the length of the sequence `from`
   */
  def apply(to: Ty, from: Seq[Ty]): Ty = from.foldRight(to)(_ ->: _)

  /**
   * Interprets the given type as function type.
   *
   * @param ty The type to be viewed as a function type.
   * @return Returns Some( (from, to) ) such that
   * `ty` = FunctionType(to, from).
   */
  def unapply(ty: Ty): Option[(Ty, List[Ty])] = ty match {
    case from ->: FunctionType(to, froms) => Some(to, from :: froms)
    case _                                => Some(ty, Nil)
  }
}
