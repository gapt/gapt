
package at.logic.utils.constraint

/** An abstract, general purpose constraint.
  *
  * Use-case: specifying the number of permissible variables during cut introduction.
  */
abstract class Constraint[+A]
object NoConstraint extends Constraint[Nothing]
case class ExactBound[+A](value: A) extends Constraint[A]
case class UpperBound[+A](value: A) extends Constraint[A]
case class LowerBound[+A](value: A) extends Constraint[A]
case class AndBound[+A](c1: Constraint[A], c2: Constraint[A])
case class OrBound[+A](c1: Constraint[A], c2: Constraint[A])
case class NotBound[+A](c1: Constraint[A])
case class ImplBound[+A](c1: Constraint[A], c2: Constraint[A])