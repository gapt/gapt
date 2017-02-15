package at.logic.gapt.utils
import scala.util.Right

object EitherHelpers {

  implicit class RichEither[A, B]( val disj: Either[A, B] ) extends AnyVal {
    def get: B = ( disj: @unchecked ) match { case Right( b ) => b }
  }

}
