package at.logic.gapt.expr

/**
 * Helper class for logical constants.
 *
 * The logical constans are the propositional connectives, the quantifiers, bottom, top, and the equality constant.
 * A logical constant is different from an expression consisting of only this logical constant, as the expression
 * is an object of type Expr and needs to have a definite type.
 *
 * A logical constant consists of a name (e.g. "∀"), and a set of possible types, (e.g. (Ti->To)->To,
 * ((Ti->Ti)->To)->To, ...).  Subclasses need to implement the function matchType, which matches these possible types.
 * This way we can handle the parametric types of the quantifiers.
 *
 * @param name  The name of this logical constant, e.g. "∀"
 */
abstract class LogicalC( val name: String )

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

object AndC extends MonomorphicLogicalC( "∧", To ->: To ->: To )
object OrC extends MonomorphicLogicalC( "∨", To ->: To ->: To )
object ImpC extends MonomorphicLogicalC( "→", To ->: To ->: To )
object NegC extends MonomorphicLogicalC( "¬", To ->: To )
object BottomC extends MonomorphicLogicalC( "⊥", To )
object TopC extends MonomorphicLogicalC( "⊤", To )

object ExistsC extends QuantifierC( "∃" )
object ForallC extends QuantifierC( "∀" )

object EqC extends LogicalC( "=" ) {
  def apply( ty: Ty ) = Const( name, ty ->: ty ->: To, ty :: Nil )

  def unapply( e: Expr ): Option[Ty] = e match {
    case Const( n, t, ps ) => unapply( ( n, t, ps ) )
    case _                 => None
  }
  def unapply( p: ( String, Ty, List[Ty] ) ): Option[Ty] =
    p match {
      case ( `name`, ty_ ->: ty__ ->: To, ty :: Nil ) if ty == ty_ && ty_ == ty__ => Some( ty )
      case _ => None
    }
}

