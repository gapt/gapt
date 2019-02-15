package gapt.expr.formula.constants

import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.ty.Ty

/**
 * Logical constant with a fixed type.
 *
 * @param name  The name of this logical constant, e.g. "∧"
 * @param ty  The fixed type of this logical constant, e.g. To->To->To
 */
class MonomorphicLogicalC( name: String, val ty: Ty ) extends LogicalC( name ) {
  private lazy val singleton = Const( name, ty )
  def apply() = singleton
  def unapply( e: Expr ): Boolean = singleton == e
  def unapply( p: ( String, Ty, List[Ty] ) ): Boolean = p._1 == name && p._2 == ty && p._3.isEmpty
}
