package at.logic.gapt.language.fol.replacements

import at.logic.gapt.expr.{ FOLExpression, LambdaExpression }
import at.logic.gapt.language.hol.HOLPosition

/**
 * Created by cthulhu on 18.06.14.
 */

/**
 * Returns a specific subterm within a position.
 *
 * This is a wrapper around the hol version.
 */
@deprecated
object getAtPositionFOL {
  /**
   * Returns the subterm at expression | pos
   * @param expression An arbitrary hol expression
   * @param pos A path of branchings in the term tree. Nil is the root position, 1 is the first argument  etc.
   * @return The subterm, if it exists.
   */
  def apply( expression: FOLExpression, pos: List[Int] ): FOLExpression =
    expression( HOLPosition( pos ) ).asInstanceOf[FOLExpression]
}

/**
 * Calculates a list of all subterms of an expression together with their respective positions.
 *
 * This is a wrapper around hol's getAllPositions2.
 */
@deprecated
object getAllPositionsFOL {
  /**
   * Calculates a list of all subterms of an expression together with their respective positions.
   * @param expression an arbitrary hol epxression
   * @return a list of pairs (position, subterm)
   */
  def apply( expression: FOLExpression ): List[Tuple2[List[Int], FOLExpression]] =
    HOLPosition.getPositions( expression )
      .flatMap { p =>
        expression.get( p ) match {
          case Some( e: FOLExpression ) => Some( p.toList -> e )
          case _                        => None
        }
      }
}
