package at.logic.gapt.proofs.lkt

import at.logic.gapt.expr.Polarity._
import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context
import at.logic.gapt.utils.Maybe

object check {
  private def requireEq( a: Expr, b: Expr ): Unit =
    require( a == b, ( -( a === b ) ).toUntypedString )
  def apply( p: LKt, lctx: LocalCtx )( implicit ctx: Maybe[Context] ): Unit = {
    p match {
      case Cut( f, q1, q2 ) =>
        require( q1.aux.inSuc && q2.aux.inAnt )
        ctx.foreach( _.check( f ) )
        check( q1.p, lctx.up1( p ) )
        check( q2.p, lctx.up2( p ) )
      case Ax( main1, main2 ) =>
        require( main1.inAnt && main2.inSuc )
        requireEq( lctx( main1 ), lctx( main2 ) )
      case Rfl( main ) =>
        require( main.inSuc )
        lctx( main ) match { case Eq( t, s ) => require( t == s ) }
      case TopR( main ) =>
        requireEq( lctx( main ), if ( main.inSuc ) Top() else Bottom() )
      case NegR( main, q ) =>
        require( main.inSuc && q.aux.inAnt )
        check( q.p, lctx.up1( p ) )
      case NegL( main, q ) =>
        require( main.inAnt && q.aux.inSuc )
        check( q.p, lctx.up1( p ) )
      case AndR( main, q1, q2 ) =>
        ( lctx( main ), main.polarity, q1.aux.polarity, q2.aux.polarity ) match {
          case ( And( _, _ ), InSuccedent, InSuccedent, InSuccedent )   =>
          case ( Or( _, _ ), InAntecedent, InAntecedent, InAntecedent ) =>
          case ( Imp( _, _ ), InAntecedent, InSuccedent, InAntecedent ) =>
        }
        check( q1.p, lctx.up1( p ) )
        check( q2.p, lctx.up2( p ) )
      case AndL( main, q ) =>
        ( lctx( main ), main.polarity, q.aux1.polarity, q.aux2.polarity ) match {
          case ( And( _, _ ), InAntecedent, InAntecedent, InAntecedent ) =>
          case ( Or( _, _ ), InSuccedent, InSuccedent, InSuccedent )     =>
          case ( Imp( _, _ ), InSuccedent, InAntecedent, InSuccedent )   =>
        }
        check( q.p, lctx.up1( p ) )
      case AllL( main, term, q ) =>
        require( main.inSuc == q.aux.inSuc )
        lctx( main ) match {
          case All( _, _ ) => require( main.inAnt )
          case Ex( _, _ )  => require( main.inSuc )
        }
        ctx.foreach( _.check( term ) )
        check( q.p, lctx.up1( p ) )
      case AllR( main, ev, q ) =>
        require( main.inSuc == q.aux.inSuc )
        lctx( main ) match {
          case All( _, _ ) => require( main.inSuc )
          case Ex( _, _ )  => require( main.inAnt )
        }
        ctx.foreach( _.check( ev ) )
        check( q.p, lctx.up1( p ) )
      case p @ Eql( main, eq, _, rwCtx, _ ) =>
        require( eq.inAnt )
        requireEq( BetaReduction.betaNormalize( lctx.subst( rwCtx ).apply( lctx.eqLhs( p ) ) ), lctx( main ) )
        ctx.foreach( _.check( rwCtx ) )
        check( p.q.p, lctx.up1( p ) )
    }
    () // prevent TCO
  }
}

