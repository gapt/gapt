package at.logic.gapt.proofs.lkt

import at.logic.gapt.expr.Polarity._
import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Checkable, Context, Sequent }
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
      case p @ Eql( main, eq, _, rwCtx, q ) =>
        require( eq.inAnt )
        requireEq( BetaReduction.betaNormalize( lctx.subst( rwCtx ).apply( lctx.eqLhs( p ) ) ), lctx( main ) )
        ctx.foreach( _.check( rwCtx ) )
        check( q.p, lctx.up1( p ) )
      case AllSk( main, term0, skDef, q ) =>
        val term = lctx.subst( term0 )
        val Apps( skSym: Const, skArgs ) = term
        requireEq( BetaReduction.betaNormalize( skDef( skArgs ) ), lctx( main ) )
        for ( ctx_ <- ctx )
          require( ctx_.skolemDef( skSym ).contains( skDef ) )
        check( q.p, lctx.up1( p ) )
      case Def( main, f0, q ) =>
        val f = lctx.subst( f0 )
        for ( ctx_ <- ctx )
          Checkable.requireDefEq( lctx( main ), f )( ctx_ )
        check( q.p, lctx.up1( p ) )
      case p @ Ind( main, f0, t0, cases ) =>
        val ( f: Abs, t ) = lctx.subst( ( f0, t0 ) )
        requireEq( lctx( main ), Substitution( f.variable -> t )( f.term ) )
        for ( ctx_ <- ctx ) {
          val Some( ctrs ) = ctx_.getConstructors( p.indTy )
          require( ctrs.size == cases.size )
          for ( ( c, ctr ) <- cases.zip( ctrs ) ) {
            require( c.ctr == ctr )
            ctx_.check( c.ctr( c.evs ) )
          }
        }
        for ( ( c, i ) <- cases.zipWithIndex )
          check( c.q.p, lctx.upn( p, i ) )
      case Link( mains, name0 ) =>
        val name = lctx.subst( name0 )
        for ( ctx_ <- ctx ) {
          val declSeq = ctx_.get[Context.ProofNames].lookup( name )
          require( declSeq.nonEmpty )
          val refSeq = Sequent( for ( m <- mains ) yield lctx( m ) -> m.polarity )
          require( declSeq.contains( refSeq ) )
        }
    }
    () // prevent TCO
  }
}

