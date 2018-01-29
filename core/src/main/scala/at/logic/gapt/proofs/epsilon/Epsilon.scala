package at.logic.gapt.proofs.epsilon

import at.logic.gapt.expr._

object EpsilonC extends LogicalC( "ε" ) {
  def apply( qtype: Ty ) = Const( name, ( qtype ->: To ) ->: qtype, List( qtype ) )

  def unapply( e: Expr ): Option[Ty] = e match {
    case Const( n, t, ps ) => unapply( ( n, t, ps ) )
    case _                 => None
  }
  def unapply( p: ( String, Ty, List[Ty] ) ): Option[Ty] =
    p match {
      case ( `name`, ( qtype ->: To ) ->: qtype_, qtype__ :: Nil ) if qtype == qtype_ && qtype_ == qtype__ => Some( qtype )
      case _ => None
    }
}

object Epsilon {
  def apply( x: Var, spec: Formula ): Expr =
    App( EpsilonC( x.ty ), Abs( x, spec ) )

  def unapply( e: Expr ): Option[( Var, Formula )] = e match {
    case App( EpsilonC( _ ), Abs( x, spec: Formula ) ) => Some( ( x, spec ) )
    case _ => None
  }
}
