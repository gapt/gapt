package at.logic.language.hol

object HOLPosition {
  implicit def apply(list: List[Int]) = new HOLPosition(list)

  implicit def toList(pos: HOLPosition) = pos.list

  /** Returns a list of all well-defined positions in an expression.
   *
   * @param exp
   * @return
   */
  def getAllPositions(exp: HOLExpression): List[HOLPosition] = getSomePositions(exp, _ => true)

  /** Returns a list of positions of subexpressions that satisfy some predicate.
   *
   * @param exp
   * @param pred The predicate to be evaluated.
   * @return Positions of subexpressions satisfying pred.
   */
  def getSomePositions(exp: HOLExpression, pred: HOLExpression => Boolean): List[HOLPosition] = exp match {
    case HOLApp(HOLApp(_, left), right) =>
      val posLeft: List[HOLPosition] = getSomePositions(left, pred) map { l => apply(1 :: l)}
      val posRight: List[HOLPosition] = getSomePositions(right, pred) map { l => apply(2 :: l)}
      if (pred(exp)) Nil :: posLeft ++ posRight else posLeft ++ posRight

    case Atom(_, args) =>
      val n = args.length
      val subPositions = for (i <- 1 to n) yield {
        getSomePositions(args(i), pred) map { l => apply(i :: l)}
      }
      if (pred(exp)) Nil :: subPositions.flatten.toList else subPositions.flatten.toList

    case Function(_, args, _) =>
      val n = args.length
      val subPositions = for (i <- 1 to n) yield {
        getSomePositions(args(i), pred) map { l => apply(i :: l)}
      }
      if (pred(exp)) Nil :: subPositions.flatten.toList else subPositions.flatten.toList
  }
}

class HOLPosition(val list: List[Int])