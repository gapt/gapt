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
abstract class LogicalC( val name: String ) {
  protected type MatchResult
  protected def matchType( exptype: Ty ): MatchResult
  protected def noMatch: MatchResult

  def unapply( exp: Expr ): MatchResult = exp match {
    case Const( `name`, exptype ) => matchType( exptype )
    case _                        => noMatch
  }
  private[expr] def unapply( pair: ( String, Ty ) ): MatchResult = pair match {
    case ( `name`, ty ) => matchType( ty )
    case _              => noMatch
  }
}

/**
 * Logical constant with a fixed type.
 *
 * @param name  The name of this logical constant, e.g. "∧"
 * @param ty  The fixed type of this logical constant, e.g. To->To->To
 */
class MonomorphicLogicalC( name: String, val ty: Ty ) extends LogicalC( name ) {
  def apply() = Const( name, ty )

  protected type MatchResult = Boolean
  protected override def matchType( exptype: Ty ) = exptype == ty
  protected override def noMatch = false
}

/**
 * A logical constant describing a quantifier, which is of type (α->To)->To.
 *
 * @param name  The name of this logical constant, e.g. "∀"
 */
class QuantifierC( name: String ) extends LogicalC( name ) {
  def apply( qtype: Ty ) = Const( name, ( qtype ->: To ) ->: To )

  protected type MatchResult = Option[Ty]
  protected override def matchType( exptype: Ty ) = exptype match {
    case ( qtype ->: To ) ->: To => Some( qtype )
    case _                       => None
  }
  protected override def noMatch = None
}

object AndC extends MonomorphicLogicalC( "∧", To ->: To ->: To )
object OrC extends MonomorphicLogicalC( "∨", To ->: To ->: To )
object ImpC extends MonomorphicLogicalC( "⊃", To ->: To ->: To )
object NegC extends MonomorphicLogicalC( "¬", To ->: To )
object BottomC extends MonomorphicLogicalC( "⊥", To )
object TopC extends MonomorphicLogicalC( "⊤", To )

object ExistsC extends QuantifierC( "∃" )
object ForallC extends QuantifierC( "∀" )

object EqC extends LogicalC( "=" ) {
  def apply( ty: Ty ) = Const( name, ty ->: ty ->: To )

  protected type MatchResult = Option[Ty]
  protected override def matchType( exptype: Ty ) = exptype match {
    case ty ->: ty_ ->: To if ty == ty_ => Some( ty )
    case _                              => None
  }
  protected override def noMatch = None
}

