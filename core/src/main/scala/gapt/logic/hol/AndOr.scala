package gapt.logic.hol

import gapt.expr.formula.{ And, Formula, MonoidalBinaryPropConnectiveHelper, Or }

object AndOr {
  def unapply( formula: Formula ): Option[( Formula, Formula, MonoidalBinaryPropConnectiveHelper )] =
    formula match {
      case And( alpha, beta ) => Some( ( alpha, beta, And ) )
      case Or( alpha, beta )  => Some( ( alpha, beta, Or ) )
      case _                  => None
    }
}