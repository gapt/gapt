package at.logic.gapt.proofs.lkt

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Context, ImmutableContext }

class unfoldInduction( ctx0: ImmutableContext ) {
  implicit val ctx = ctx0
  var unfolded = false

  def apply( b: Bound1 ): Bound1 = b.copy( p = apply( b.p ) )
  def apply( b: Bound2 ): Bound2 = b.copy( p = apply( b.p ) )
  def apply( b: BoundN ): BoundN = b.copy( p = apply( b.p ) )

  def apply( p: LKt ): LKt = p match {
    case Cut( f, q1, q2 )                                 => Cut( f, apply( q1 ), apply( q2 ) )
    case Ax( _, _ ) | Rfl( _ ) | TopR( _ ) | Link( _, _ ) => p
    case NegR( main, q )                                  => NegR( main, apply( q ) )
    case NegL( main, q )                                  => NegL( main, apply( q ) )
    case AndR( main, q1, q2 )                             => AndR( main, apply( q1 ), apply( q2 ) )
    case AndL( main, q )                                  => AndL( main, apply( q ) )
    case AllL( main, term, q )                            => AllL( main, term, apply( q ) )
    case AllR( main, ev, q )                              => AllR( main, ev, apply( q ) )
    case Eql( main, eq, ltr, rwCtx, q )                   => Eql( main, eq, ltr, rwCtx, apply( q ) )
    case AllSk( main, term, skDef, q )                    => AllSk( main, term, skDef, apply( q ) )
    case Def( main, f, q )                                => Def( main, f, apply( q ) )
    case p @ Ind( main, f, term, cases ) =>
      val Some( ctrs ) = ctx.getConstructors( p.indTy )
      term match {
        case Apps( ctr: Const, as ) if ctrs.contains( ctr ) =>
          unfolded = true
          // we need a proof of ⊢ main: φ(c(as))
          val i = ctrs.indexOf( ctr )
          val ci = cases( i )
          var r = apply( Substitution( ci.evs zip as )( ci.q.p.replace( ci.q.auxs.head, main ) ) )
          for ( ( aux, recOcc ) <- ci.q.auxs.tail.zip( as.filter( _.ty == p.indTy ) ) )
            r = Cut(
              BetaReduction.betaNormalize( f( recOcc ) ).asInstanceOf[Formula],
              Bound1( main, apply( Ind( main, f, recOcc, cases ) ) ),
              Bound1( aux, r ) )
          r
        case _ =>
          Ind( main, f, term, cases.map( c => c.copy( q = apply( c.q ) ) ) )
      }
  }
}

object unfoldInduction {
  def apply( p: LKt )( implicit ctx: Context ): Option[LKt] = {
    val ui = new unfoldInduction( ctx.toImmutable )
    val result = ui( p )
    if ( ui.unfolded ) Some( result ) else None
  }
}
