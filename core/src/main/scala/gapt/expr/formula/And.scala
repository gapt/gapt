package gapt.expr.formula

import gapt.expr.formula.constants.AndC
import gapt.expr.formula.constants.TopC

object And extends MonoidalBinaryPropConnectiveHelper( AndC, TopC ) {
  object Flat {
    /**
     * Retrieves the outermost conjuncts of a formula.
     *
     * @param formula The formula whose conjuncts are to be retrieved.
     * @return The outermost conjuncts of the formula.
     */
    def unapply( formula: Formula ): Option[Seq[Formula]] = formula match {
      case And( Flat( left ), Flat( right ) ) => Some( left ++ right )
      case _                                  => Some( Seq( formula ) )
    }
  }
}
