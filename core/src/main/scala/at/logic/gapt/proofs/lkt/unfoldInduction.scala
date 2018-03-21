package at.logic.gapt.proofs.lkt

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Context, ImmutableContext }
import at.logic.gapt.provers.simp.{ SimpEqResult, Simplifier }

trait SimpAdapter {
  def hyps: Set[Hyp]
  def simpEq( target: Expr ): Option[( Bound1, Expr )]
}

case object NoopSimpAdapter extends SimpAdapter {
  def hyps: Set[Hyp] = Set()
  def simpEq( target: Expr ): Option[( Bound1, Expr )] = None
}

case class SimplifierSimpAdapter( simp: Simplifier, lctx: LocalCtx ) extends SimpAdapter {
  def hyps = lctx.hyps.keySet.filter( _.inAnt )
  def simpEq( target: Expr ): Option[( Bound1, Expr )] = {
    simp.simpEqToEql( target ) match {
      case SimpEqResult.Refl( _ ) => None
      case SimpEqResult.Prf( lk, lhs, rhs ) =>
        val eqHyp = lctx.hyps.keySet.freshSuc
        val lctx2 = lctx.updated( eqHyp, lhs === rhs )
        val lkt = LKToLKt.forLCtx( lk, lctx2, debugging = true )
        Some( Bound1( eqHyp, lkt ), rhs )
    }
  }
}

class unfoldInduction( simp: SimpAdapter, ctx0: ImmutableContext ) {
  implicit val ctx = ctx0
  var unfolded = false

  val simpHyps = simp.hyps

  def apply( b0: Bound1 ): Bound1 = {
    val b = b0.rename_( simpHyps )
    b.copy( p = apply( b.p ) )
  }
  def apply( b0: Bound2 ): Bound2 = {
    val b = b0.rename_( simpHyps )
    b.copy( p = apply( b.p ) )
  }
  def apply( b0: BoundN ): BoundN = {
    val b = b0.rename_( simpHyps )
    b.copy( p = apply( b.p ) )
  }

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
    case p @ Ind( main, f, term, cases0 ) =>
      val cases = cases0.map( c => c.copy( q = c.q.rename_( simpHyps union p.freeHyps ) ) )
      val Some( ctrs ) = ctx.getConstructors( p.indTy )
      assert( !simpHyps( main ) )
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
          simp.simpEq( term ) match {
            case Some( ( simpPrf, newTerm ) ) =>
              val eqHyp = ( p.freeHyps union simpHyps ).freshAnt
              Cut( term === newTerm, simpPrf,
                Bound1(
                  eqHyp,
                  Eql( main, eqHyp, ltr = true, f,
                    Bound1( main, apply( Ind( main, f, newTerm, cases ) ) ) ) ) )
            case _ =>
              Ind( main, f, term, cases.map( c => c.copy( q = apply( c.q ) ) ) )
          }
      }
  }
}

object unfoldInduction {
  def apply( p: LKt )( implicit ctx: Context ): Option[LKt] = apply( p, NoopSimpAdapter )

  def apply( p: LKt, simp: SimpAdapter )( implicit ctx: Context ): Option[LKt] = {
    val ui = new unfoldInduction( simp, ctx.toImmutable )
    val result = ui( p )
    if ( ui.unfolded ) Some( result ) else None
  }
}
