package gapt.utils
import scala.util.Right

object EitherHelpers {

  implicit class RichEither[A, B](private val disj: Either[A, B]) extends AnyVal {
    def get: B = (disj: @unchecked) match { case Right(b) => b }
  }

}

import scala.util.boundary
extension [A, B](e: Either[A, B]) {

  /** Returns the value of this `Either` if it is a `Right`, otherwise breaks the current boundary with the value as a `Left`.
  * This allows to concise error handling code that can propagate values up, e.g.
  *
  * def possiblyFailingInt: Either[String, Int] = Left("error")
  *
  * def possiblyFailingPlusTwo: Either[String, Int] = boundary {
  *   val value: Int = possiblyFailingInt.getOrBreak
  *   Right(value + 2)
  * }
  *
  * assert(possiblyFailingPlusTwo == Left("error"))
  */
  def getOrBreak[B1 <: B](using label: boundary.Label[Either[A, B1]]): B = e match {
    case Right(value) => value
    case Left(value)  => boundary.break(Left(value))(using label)
  }
}
