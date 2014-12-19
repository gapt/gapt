package at.logic.language.hol

import at.logic.language.lambda.LambdaPosition


object HOLPosition {
  implicit def apply(list: List[Int]) = new HOLPosition(list)

  def apply(is: Int*) = new HOLPosition(is.toList)

  implicit def toList(pos: HOLPosition) = pos.list


  /** Returns a list of positions of subexpressions that satisfy some predicate.
    *
    * This function is a wrapper around [[at.logic.language.lambda.LambdaPosition.getPositions]].
    * @param exp The expression under consideration.
    * @param pred The predicate to be evaluated. Defaults to "always true", i.e. if called without this argument, the function will return all positions.
    * @return Positions of subexpressions satisfying pred.
    */
  def getPositions(exp: HOLExpression, pred: HOLExpression => Boolean = _ => true): List[HOLPosition] = {
    LambdaPosition.getPositions(exp, pred) filter { definesHOLPosition(exp) } map { toHOLPosition(exp) }
  }

  /** Replaces a a subexpression in a HOLExpression. This function is actually a wrapper around [[at.logic.language.lambda.LambdaPosition.replace]].
    *
    * @param exp The expression in which to perform the replacement.
    * @param pos The position at which to replace.
    * @param repTerm The expression that exp(pos) should be replaced with.
    * @return
    */
  def replace(exp: HOLExpression, pos: HOLPosition, repTerm: HOLExpression) = LambdaPosition.replace(exp, toLambdaPosition(exp)(pos), repTerm).asInstanceOf[HOLExpression]

  /** Compares to HOLExpressions and returns the list of outermost positions where they differ.
    *
    * @param exp1 The first expression.
    * @param exp2 The second expression.
    * @return The list of outermost positions at which exp1 and exp2 differ.
    */
  def differingPositions(exp1: HOLExpression, exp2: HOLExpression): List[HOLPosition] = LambdaPosition.differingPositions(exp1, exp2) map { toHOLPosition(exp1) }

  /** Converts a HOLPosition into the corresponding LambdaPosition.
    *
    * Note that position conversion is always relative to a given expression.
    * @param pos The position to be converted.
    * @param exp The relevant HOLExpression.
    * @return The corresponding LambdaPosition.
    */
  def toLambdaPosition(exp: HOLExpression)(pos: HOLPosition): LambdaPosition = toLambdaPositionOption(exp)(pos) match {
    case Some(p) => p
    case None => throw new Exception("Can't convert position "+pos+" for expression "+exp+" to LambdaPosition.")
  }

  /** Converts a HOLPosition into the corresponding LambdaPosition, if one exists.
    *
    * Note that position conversion is always relative to a given expression.
    * @param pos The position to be converted.
    * @param exp The relevant HOLExpression.
    * @return The corresponding LambdaPosition.
    */
  def toLambdaPositionOption(exp: HOLExpression)(pos: HOLPosition): Option[LambdaPosition] = {
    if (pos.isEmpty) Some(Nil)
    else {
      val rest = pos.tail
      (pos.head, exp) match {
        case (1, Neg(subExp)) =>
          toLambdaPositionOption(subExp)(rest) match {
            case Some(subPos) => Some(2  :: subPos)
            case None => None
          }

        case (_, Neg(_)) => None

        case (1, ExVar(_, subExp)) =>
         toLambdaPositionOption(subExp)(rest) match {
            case Some(subPos) => Some(2 :: 1 :: subPos)
            case None => None
          }

        case (_, ExVar(_,_)) => None

        case (1, AllVar(_, subExp)) =>
          toLambdaPositionOption(subExp)(rest) match {
            case Some(subPos) => Some(2 :: 1 :: subPos)
            case None => None
          }

        case (1, BinaryConnective(left, _)) =>
          toLambdaPositionOption(left)(rest) match {
            case Some(leftPos) => Some(1 :: 2 :: leftPos)
            case None => None
          }


        case (2, BinaryConnective(_, right)) =>
          toLambdaPositionOption(right)(rest) match {
            case Some(rightPos) => Some(2 :: rightPos)
            case None => None
          }

        case (_, BinaryConnective(_,_)) => None

        case (1, HOLApp(f,_)) => toLambdaPositionOption(f)(rest) match {
          case Some(subPos) => Some(1 :: subPos)
          case None => None
        }


        case (2, HOLApp(_, arg)) => toLambdaPositionOption(arg)(rest) match {
          case Some(subPos) => Some(2 :: subPos)
          case None => None
        }

        case (1, HOLAbs(_, term)) => toLambdaPositionOption(term)(rest) match {
          case Some(subPos) => Some(1 :: subPos)
          case None => None
        }

        case _ => None
      }
    }
  }

  /** Converts a LambdaPosition into the corresponding HOLPosition.
    *
    * Note that position conversion is always relative to a given expression.
    * @param pos The position to be converted.
    * @param exp The relevant HOLExpression.
    * @return The corresponding HOLPosition.
    */
  def toHOLPosition(exp: HOLExpression)(pos: LambdaPosition): HOLPosition = {
    if (pos.isEmpty) Nil
    else {
      val rest = pos.tail
      exp match {
        case Neg(subExp) =>
          if (pos.head == 2)
            1 :: toHOLPosition(subExp)(rest)
          else
            throw new Exception("Can't convert position "+pos+" for expression "+exp+" to HOLPosition.")

        case BinaryConnective(left, right)  =>
          if (pos.head == 1 && rest.headOption == Some(2))
            1 :: toHOLPosition(left)(rest.tail)
          else if (pos.head == 2)
            2 :: toHOLPosition(right)(rest)
          else throw new Exception("Can't convert position "+pos+" for expression "+exp+" to HOLPosition.")

        case ExVar(_, subExp) =>
          if (pos.head == 2 && rest.headOption == Some(1))
            1 :: toHOLPosition(subExp)(rest.tail)
          else throw new Exception("Can't convert position "+pos+" for expression "+exp+" to HOLPosition.")

        case AllVar(_, subExp) =>
          if (pos.head == 2 && rest.headOption == Some(1))
            1 :: toHOLPosition(subExp)(rest.tail)
          else throw new Exception("Can't convert position "+pos+" for expression "+exp+" to HOLPosition.")

        case HOLApp(f, arg) =>
          if (pos.head == 1)
            1 :: toHOLPosition(f)(rest)
          else if (pos.head == 2)
            2 :: toHOLPosition(arg)(rest)
          else throw new Exception("Can't convert position "+pos+" for expression "+exp+" to HOLPosition.")

        case HOLAbs(_, term) =>
          if (pos.head == 1)
            1 :: toHOLPosition(term)(rest)
          else throw new Exception("Can't convert position "+pos+" for expression "+exp+" to HOLPosition.")

        case _ => throw new Exception("Can't convert position "+pos+" for expression "+exp+" to HOLPosition.")
      }
    }
  }

  /** Tests whether a LambdaPosition denotes a HOLPosition for the given expression.
   *
   * @param exp
   * @param pos
   * @return
   */
  def definesHOLPosition(exp: HOLExpression)(pos: LambdaPosition): Boolean = {
    if (pos.isEmpty) true
    else {
      val rest = pos.tail
      exp match {
        case Neg(subExp) =>
          if (pos.head == 2)
            definesHOLPosition(subExp)(rest)
          else
            false

        case BinaryConnective(left, right)  =>
          if (pos.head == 1 && rest.headOption == Some(2))
            definesHOLPosition(left)(rest.tail)
          else if (pos.head == 2)
            definesHOLPosition(right)(rest)
          else false

        case ExVar(_, subExp) =>
          if (pos.head == 2 && rest.headOption == Some(1))
            definesHOLPosition(subExp)(rest.tail)
          else false

        case AllVar(_, subExp) =>
          if (pos.head == 2 && rest.headOption == Some(1))
            definesHOLPosition(subExp)(rest.tail)
          else false

        case HOLApp(f, arg) =>
          if (pos.head == 1)
            definesHOLPosition(f)(rest)
          else if (pos.head == 2)
            definesHOLPosition(arg)(rest)
          else false

        case HOLAbs(_, term) =>
          if (pos.head == 1)
            definesHOLPosition(term)(rest)
          else false

        case _ => false
      }
    }
  }
}
/** Represents a position in a [[at.logic.language.hol.HOLExpression]].
 *
  * Positions are given as lists of Integers. The empty list denotes the current expression itself.
  * A list starting with k denotes a subexpression in the k^th^ argument of the current expression.
 * @param list The list describing the position.
 */
class HOLPosition(val list: List[Int]){
  require(list.forall(i => i == 1 || i == 2))
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
    case p: HOLPosition => p.list == list
    case _ => false
  }

  override def hashCode() = list.hashCode()
}

object BinaryConnective {
  def unapply(exp: HOLExpression) = exp match {
    case And(l,r) => Some(l,r)
    case Or(l,r) => Some(l,r)
    case Imp(l,r) => Some(l,r)
    case Equation(l,r) => Some(l,r)
    case _ => None
  }
}