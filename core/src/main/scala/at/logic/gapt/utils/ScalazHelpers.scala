package at.logic.gapt.utils
import scalaz._

object ScalazHelpers {

  implicit class RichOr[A, B]( val disj: A \/ B ) extends AnyVal {
    def get: B = ( disj: @unchecked ) match { case \/-( b ) => b }
  }

}
