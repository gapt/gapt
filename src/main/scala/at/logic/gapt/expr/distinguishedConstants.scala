package at.logic.gapt.expr
import types._
import symbols._

abstract class LogicalC( val name: String ) {
  val symbol = StringSymbol( name )

  private[expr]type MatchResult
  private[expr] def matchType( exptype: TA ): MatchResult
  private[expr] def noMatch: MatchResult

  def unapply( exp: LambdaExpression ): MatchResult = exp match {
    case Const( `name`, exptype ) => matchType( exptype )
    case _                        => noMatch
  }
  private[expr] def unapply( pair: ( SymbolA, TA ) ): MatchResult = pair match {
    case ( `symbol`, ty ) => matchType( ty )
    case _                => noMatch
  }
}

class MonomorphicLogicalC( name: String, val ty: TA ) extends LogicalC( name ) {
  def apply() = Const( symbol, ty )

  private[expr]type MatchResult = Boolean
  private[expr] override def matchType( exptype: TA ) = exptype == ty
  private[expr] override def noMatch = false
}

class QuantifierC( name: String ) extends LogicalC( name ) {
  def apply( qtype: TA ) = Const( symbol, ( qtype -> To ) -> To )

  private[expr]type MatchResult = Option[TA]
  private[expr] override def matchType( exptype: TA ) = exptype match {
    case ( qtype -> To ) -> To => Some( qtype )
    case _                     => None
  }
  private[expr] override def noMatch = None
}

object AndC extends MonomorphicLogicalC( "∧", To -> ( To -> To ) )
object OrC extends MonomorphicLogicalC( "∨", To -> ( To -> To ) )
object ImpC extends MonomorphicLogicalC( "⊃", To -> ( To -> To ) )
object NegC extends MonomorphicLogicalC( "¬", To -> To )
object BottomC extends MonomorphicLogicalC( "⊥", To )
object TopC extends MonomorphicLogicalC( "⊤", To )

object ExistsC extends QuantifierC( "∃" )
object ForallC extends QuantifierC( "∀" )

object EqC extends LogicalC( "=" ) {
  def apply( ty: TA ) = Const( symbol, ty -> ( ty -> To ) )

  private[expr]type MatchResult = Option[TA]
  private[expr] override def matchType( exptype: TA ) = exptype match {
    case ty -> ( ty_ -> To ) if ty == ty_ => Some( ty )
    case _                                => None
  }
  private[expr] override def noMatch = None
}

//package schematic {
//
//  object BigAndC extends MonomorphicLogicalC( "⋀", ( Tindex -> To ) -> ( Tindex -> ( Tindex -> To ) ) )
//  object BigOrC extends MonomorphicLogicalC( "⋁", ( Tindex -> To ) -> ( Tindex -> ( Tindex -> To ) ) )
//
//  object ZeroC extends MonomorphicLogicalC( "0", Tindex )
//  object SuccC extends MonomorphicLogicalC( "s", Tindex -> Tindex )
//
//  object PlusC extends MonomorphicLogicalC( "+", Tindex -> ( Tindex -> Tindex ) )
//  object TimesC extends MonomorphicLogicalC( "×", Tindex -> ( Tindex -> Tindex ) )
//
//  object BiggerThanC extends MonomorphicLogicalC( ">", Tindex -> ( Tindex -> To ) )
//  object SimC extends MonomorphicLogicalC( "~", Tindex -> ( Tindex -> To ) )
//  object LessThanC extends MonomorphicLogicalC( "<", Tindex -> ( Tindex -> To ) )
//  object LeqC extends MonomorphicLogicalC( "≤", Tindex -> ( Tindex -> To ) )
//
//}