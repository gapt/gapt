/** This file contains code for positions and replacements in LambdaExpressions.

 */

package at.logic.language.lambda

object LambdaPosition {
  implicit def apply(list: List[Int]) = new LambdaPosition(list)
  def apply(xs: Int*) = new LambdaPosition(xs.toList)
  implicit def toList(p: LambdaPosition) = p.list

  /** Returns a list of positions of subexpressions that satisfy some predicate.
    *
    * @param exp The expression under consideration.
    * @param pred The predicate to be evaluated. Defaults to "always true", i.e. if called without this argument, the function will return all positions.
    * @return Positions of subexpressions satisfying pred.
    */
  def getPositions[T <: LambdaExpression](exp: T, pred: T => Boolean = (x: T) => true): List[LambdaPosition] = exp match {
    case Var(_,_) | Const(_,_) => if (pred(exp)) List(Nil) else Nil
    case App(f, arg) =>
      val fPositions = getPositions(f.asInstanceOf[T], pred) map {p => LambdaPosition(1 :: p)}
      val argPositions = getPositions(arg.asInstanceOf[T], pred) map {p => LambdaPosition(2 :: p)}

      if (pred(exp)) Nil :: fPositions ::: argPositions else fPositions ::: argPositions

    case Abs(_, subExp) =>
      val subPositions = getPositions(subExp.asInstanceOf[T], pred) map {p => LambdaPosition(1 :: p)}

      if (pred(exp)) Nil :: subPositions else subPositions

    case _ => throw new IllegalArgumentException("This case is not handled.")
  }

  /** Compares to LambdaExpressions and returns the list of outermost positions where they differ.
   *
   * @param exp1 The first expression.
   * @param exp2 The second expression.
   * @return The list of outermost positions at which exp1 and exp2 differ.
   */
  def differingPositions(exp1: LambdaExpression, exp2: LambdaExpression): List[LambdaPosition] = (exp1, exp2) match {
    case (Var(n1, t1), Var(n2, t2)) if n1 == n2 && t1 == t2 => Nil
    case (Const(n1, t1), Const(n2, t2)) if n1 == n2 && t1 == t2 => Nil
    case (App(f1, arg1), App(f2, arg2)) =>
      val list1 = differingPositions(f1, f2) map { p => LambdaPosition(1 :: p) }
      val list2 = differingPositions(arg1, arg2) map { p => LambdaPosition(2 :: p) }
      list1 ++ list2
    case (Abs(v1, term1), Abs(v2, term2)) if v1 == v2 =>
     differingPositions(term1, term2) map { p => LambdaPosition(1 :: p) }
    case _ => List(Nil)
  }

  /** Replaces a a subexpression in a LambdaExpression.
    *
    * @param exp The expression in which to perform the replacement.
    * @param pos The position at which to replace.
    * @param repTerm The expression that exp(pos) should be replaced with.
    * @return
    */
  def replace(exp: LambdaExpression, pos: LambdaPosition, repTerm: LambdaExpression): LambdaExpression =
    if (pos.isEmpty)
        repTerm
    else {
      val rest = pos.tail
      exp match {
        case Abs(t, subExp) if pos.head == 1 => Abs(t, replace(subExp, rest, repTerm))
        case App(f, arg) if pos.head == 1 => App(replace(f, rest, repTerm), arg)
        case App(f, arg) if pos.head == 2 => App(f, replace(arg, rest, repTerm))
        case _ => throw new IllegalArgumentException("Not possible to replace at position "+pos+" in expression "+exp+".")
      }
    }

}

/** Represents a position in a [[at.logic.language.lambda.LambdaExpression]].
 *
  * Positions are represented by lists of Integers. The empty list denotes the expression itself.
  * A nonempty list denotes a position in the left or right subexpression according to whether it starts with 1 or 2.
  *
 * @param list The list of integers describing the position.
 */
class LambdaPosition(val list: List[Int]) {
  require(list.forall(i => i == 1 || i == 2))

  def toList = list
  def head = list.head
  def tail = list.tail
  def isEmpty = list.isEmpty
  override def toString = "["+toString_(list)

  private def toString_(xs: List[Int]): String = xs match {
    case Nil => "]"
    case x :: Nil =>
      x.toString +"]"
    case x :: ys => x.toString+", "+toString_(ys)
  }

  override def equals(that: Any) = that match {
    case p: LambdaPosition => p.list == list
    case _ => false
  }

  override def hashCode() = list.hashCode()
}