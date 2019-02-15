package gapt.expr.formula.constants

import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.ty.->:
import gapt.expr.ty.To
import gapt.expr.ty.Ty

/**
 * A logical constant describing a quantifier, which is of type (α->To)->To.
 *
 * @param name  The name of this logical constant, e.g. "∀"
 */
class QuantifierC( name: String ) extends LogicalC( name ) {
  def apply( qtype: Ty ) = Const( name, ( qtype ->: To ) ->: To, List( qtype ) )

  def unapply( e: Expr ): Option[Ty] = e match {
    case Const( n, t, ps ) => unapply( ( n, t, ps ) )
    case _                 => None
  }
  def unapply( p: ( String, Ty, List[Ty] ) ): Option[Ty] =
    p match {
      case ( `name`, ( qtype_ ->: To ) ->: To, qtype :: Nil ) if qtype == qtype_ => Some( qtype )
      case _ => None
    }
}
