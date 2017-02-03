package at.logic.gapt.utils
import scala.util.{ Left, Right }
import scalaz._

object ScalazHelpers {

  implicit class RichOr[A, B]( val disj: A \/ B ) extends AnyVal {
    def get: B = ( disj: @unchecked ) match { case \/-( b ) => b }
  }

  implicit class RichEither[A, B]( val disj: Either[A, B] ) extends AnyVal {
    def get: B = ( disj: @unchecked ) match { case Right( b ) => b }

    def leftMap[A_]( f: A => A_ ): Either[A_, B] =
      disj match {
        case Left( error )  => Left( f( error ) )
        case Right( value ) => Right( value )
      }
  }

}
