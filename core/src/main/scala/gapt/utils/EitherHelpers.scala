package gapt.utils
import scala.util.Right

object EitherHelpers {

  implicit class RichEither[A, B]( private val disj: Either[A, B] ) extends AnyVal {
    def get: B = ( disj: @unchecked ) match { case Right( b ) => b }
  }

}
