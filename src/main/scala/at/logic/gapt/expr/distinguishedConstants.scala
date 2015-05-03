package at.logic.gapt.expr
import types._
import symbols._

class LogicalC( val name: String, val ty: TA ) {
  val symbol = StringSymbol( name )

  def apply() = Const( symbol, ty )
  def unapply( exp: LambdaExpression ): Boolean = exp match {
    case Const( sym, exptype ) => unapply( StringSymbol( sym ), exptype )
    case _                     => false
  }
  def unapply( pair: ( SymbolA, TA ) ): Boolean = pair match {
    case ( `symbol`, `ty` ) => true
    case _                  => false
  }
}

class QuantifierC( val name: String ) {
  val symbol = StringSymbol( name )

  def apply( qtype: TA ) = Const( symbol, ( qtype -> To ) -> To )
  def unapply( exp: LambdaExpression ): Option[TA] = exp match {
    case Const( sym, exptype ) => unapply( StringSymbol( sym ), exptype )
    case _                     => None
  }
  def unapply( pair: ( SymbolA, TA ) ): Option[TA] = pair match {
    case ( `symbol`, ( qtype -> To ) -> To ) => Some( qtype )
    case _                                   => None
  }
}

object AndC extends LogicalC( "∧", To -> ( To -> To ) )
object OrC extends LogicalC( "∨", To -> ( To -> To ) )
object ImpC extends LogicalC( "⊃", To -> ( To -> To ) )
object NegC extends LogicalC( "¬", To -> To )
object BottomC extends LogicalC( "⊥", To )
object TopC extends LogicalC( "⊤", To )

object ExistsQ extends QuantifierC( "∃" )
object ForallQ extends QuantifierC( "∀" )

object EqC {
  val name = "="
  val symbol = StringSymbol( name )

  def apply( ty: TA ) = Const( symbol, ty -> ( ty -> To ) )
  def unapply( exp: LambdaExpression ): Option[TA] = exp match {
    case Const( sym, exptype ) => unapply( StringSymbol( sym ), exptype )
    case _                     => None
  }
  def unapply( pair: ( SymbolA, TA ) ): Option[TA] = pair match {
    case ( `symbol`, ty -> ( ty_ -> To ) ) if ty == ty_ => Some( ty )
    case _ => None
  }
}

//package schematic {
//
//  object BigAndC extends LogicalC( "⋀", ( Tindex -> To ) -> ( Tindex -> ( Tindex -> To ) ) )
//  object BigOrC extends LogicalC( "⋁", ( Tindex -> To ) -> ( Tindex -> ( Tindex -> To ) ) )
//
//  object ZeroC extends LogicalC( "0", Tindex )
//  object SuccC extends LogicalC( "s", Tindex -> Tindex )
//
//  object PlusC extends LogicalC( "+", Tindex -> ( Tindex -> Tindex ) )
//  object TimesC extends LogicalC( "×", Tindex -> ( Tindex -> Tindex ) )
//
//  object BiggerThanC extends LogicalC( ">", Tindex -> ( Tindex -> To ) )
//  object SimC extends LogicalC( "~", Tindex -> ( Tindex -> To ) )
//  object LessThanC extends LogicalC( "<", Tindex -> ( Tindex -> To ) )
//  object LeqC extends LogicalC( "≤", Tindex -> ( Tindex -> To ) )
//
//}