package at.logic.gapt.proofs.epsilon

import at.logic.gapt.expr._

object EpsilonC extends LogicalC( "ε" ) {
  def apply( qtype: Ty ) = Const( name, ( qtype -> To ) -> Ti )

  protected type MatchResult = Option[Ty]
  protected override def matchType( exptype: Ty ) = exptype match {
    case ( qtype -> To ) -> Ti => Some( qtype )
    case _                     => None
  }
  protected override def noMatch = None
}

object Epsilon {
  def apply( x: Var, spec: Formula ): Expr =
    App( EpsilonC( x.ty ), Abs( x, spec ) )

  def unapply( e: Expr ): Option[( Var, Formula )] = e match {
    case App( EpsilonC( _ ), Abs( x, spec: Formula ) ) => Some( ( x, spec ) )
    case _ => None
  }
}
