package gapt.expr.formula.fol

import gapt.expr.Expr
import gapt.expr.formula.fol.FOLPosition.getPositions

trait FOLExpression extends Expr {
  /**
   * Retrieves this expression's subexpression at a given position.
   *
   * @param pos The position to be retrieved.
   * @return The subexpression at pos.
   */
  def apply( pos: FOLPosition ): FOLExpression = get( pos ) match {
    case Some( f ) => f
    case None      => throw new Exception( "Position " + pos + " does not exist in expression " + this + "." )
  }

  /**
   * Retrieves this expression's subexpression at a given position, if there is one.
   *
   * @param pos The position to be retrieved.
   * @return If there is a subexpression at that position, return Some(that expression). Otherwise None.
   */
  def get( pos: FOLPosition ): Option[FOLExpression] =
    FOLPosition.toHOLPositionOption( this )( pos ).flatMap( get ).asInstanceOf[Option[FOLExpression]]

  def replace( pos: FOLPosition, replacement: FOLExpression ): FOLExpression =
    FOLPosition.replace( this, pos, replacement )

  /**
   * Tests whether this expression has a subexpression at a given position.
   *
   * @param pos The position to be tested.
   * @return Whether this(pos) is defined.
   */
  def isDefinedAt( pos: FOLPosition ): Boolean = get( pos ).isDefined

  /**
   * Finds all HOL positions of a subexpression in this expression.
   *
   * @param exp The subexpression to be found.
   * @return A list containing all positions where exp occurs.
   */
  def find( exp: FOLExpression ): List[FOLPosition] = getPositions( this, _ == exp )

}
