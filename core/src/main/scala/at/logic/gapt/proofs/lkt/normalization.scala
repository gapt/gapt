package at.logic.gapt.proofs.lkt

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.proofs.Context
import at.logic.gapt.utils.Maybe

class Normalizer[LC <: ALCtx[LC]] {
  case class Subst( hyp: Hyp, byF: Formula, by: Bound1 ) {
    def apply( bnd: Bound1, lctx: B1[LC] ): Bound1 =
      if ( bnd.aux == hyp ) bnd
      else if ( !by.freeHyps( bnd.aux ) ) Bound1( bnd.aux, apply( bnd.p, lctx( bnd.aux ) ) )
      else apply( bnd.rename( by.freeHyps ), lctx )
    def apply( bnd: Bound2, lctx: B2[LC] ): Bound2 =
      if ( bnd.aux1 == hyp || bnd.aux2 == hyp ) bnd
      else if ( !by.freeHyps( bnd.aux1 ) && !by.freeHyps( bnd.aux2 ) )
        Bound2( bnd.aux1, bnd.aux2, apply( bnd.p, lctx( bnd.aux1, bnd.aux2 ) ) )
      else apply( bnd.rename( by.freeHyps ), lctx )

    def apply( p: LKt, lctx: LC ): LKt = p match {
      case _ if !p.freeHyps( hyp ) => p
      case Cut( f, q1, q2 )        => Cut( f, apply( q1, lctx.up1_( p ) ), apply( q2, lctx.up2_( p ) ) )
      case Ax( m1, m2 ) =>
        if ( hyp == m1 ) by.inst( m2 )
        else if ( hyp == m2 ) by.inst( m1 )
        else p
      case Rfl( main ) if main != hyp     => p
      case TopR( cohyp ) if cohyp != hyp  => p
      case NegR( main, q ) if main != hyp => NegR( main, apply( q, lctx.up1_( p ) ) )
      case NegL( main, q ) if main != hyp => NegL( main, apply( q, lctx.up1_( p ) ) )
      case AndR( main, q1, q2 ) if main != hyp =>
        AndR( main, apply( q1, lctx.up1_( p ) ), apply( q2, lctx.up2_( p ) ) )
      case AndL( main, q ) if main != hyp       => AndL( main, apply( q, lctx.up12_( p ) ) )
      case AllL( main, term, q ) if main != hyp => AllL( main, term, apply( q, lctx.up1_( p ) ) )
      case AllR( main, ev, q ) if main != hyp =>
        if ( !by.p.freeVars( ev ) ) AllR( main, ev, apply( q, lctx.up1_( p ) ) ) else {
          val ev_ = rename( ev, by.p.freeVars union p.freeVars )
          apply( AllR( main, ev_, Substitution( ev -> ev_ )( q ) ), lctx )
        }
      case Eql( main, eq, ltr, rwCtx, q ) if main != hyp && eq != hyp =>
        Eql( main, eq, ltr, rwCtx, apply( q, lctx.up1_( p ) ) )
      case _ =>
        if ( hyp.inSuc ) evalCut( lctx, byF, Bound1( hyp, p ), by )
        else evalCut( lctx, byF, by, Bound1( hyp, p ) )
    }
  }

  def normalize( bnd: Bound1, lctx: LC ): Bound1 = Bound1( bnd.aux, normalize( bnd.p, lctx ) )
  def normalize( bnd: Bound2, lctx: LC ): Bound2 = Bound2( bnd.aux1, bnd.aux2, normalize( bnd.p, lctx ) )
  def normalize( p: LKt, lctx: LC ): LKt = p match {
    case _ if !p.hasCuts => p
    case Cut( f, q1, q2 ) =>
      evalCut( lctx, f, normalize( q1, lctx.up1( p ) ), normalize( q2, lctx.up2( p ) ) )
    case Ax( _, _ ) | Rfl( _ ) | TopR( _ ) => p
    case NegR( main, q )                   => NegR( main, normalize( q, lctx.up1( p ) ) )
    case NegL( main, q )                   => NegL( main, normalize( q, lctx.up1( p ) ) )
    case AndR( main, q1, q2 )              => AndR( main, normalize( q1, lctx.up1( p ) ), normalize( q2, lctx.up2( p ) ) )
    case AndL( main, q )                   => AndL( main, normalize( q, lctx.up1( p ) ) )
    case AllL( main, term, q )             => AllL( main, term, normalize( q, lctx.up1( p ) ) )
    case AllR( main, ev, q )               => AllR( main, ev, normalize( q, lctx.up1( p ) ) )
    case Eql( main, eq, ltr, rwCtx, q )    => Eql( main, eq, ltr, rwCtx, normalize( q, lctx.up1( p ) ) )
  }

  def inst( q: Bound1, byF: Formula, by: Bound1, lctx: LC ): LKt = Subst( q.aux, byF, by ).apply( q.p, lctx )
  def inst1( q: Bound2, byF: Formula, by: Bound1, lctx: LC, g1: Formula, g2: Formula ): Bound1 =
    Subst( q.aux1, byF, by ).apply( Bound1( q.aux2, q.p ), lctx.upS( g1 )( q.aux1 ).upS( g2 ) )

  def evalCut( lctx: LC, f: Formula, q1: Bound1, q2: Bound1 ): LKt =
    evalCut( Cut( f, q1, q2 ), lctx )

  def evalCut( c: Cut, lctx: LC ): LKt = {
    val Cut( f, q1, q2 ) = c
    val lctx1 = lctx.up1( c )
    val lctx2 = lctx.up2( c )
    ( q1.p, q2.p, f ) match {
      case ( _, _, _ ) if q1.isConst              => q1.p
      case ( _, _, _ ) if q2.isConst              => q2.p

      case ( Ax( h1, c1 ), _, _ ) if c1 == q1.aux => q2.inst( h1 )
      case ( _, Ax( h2, c2 ), _ ) if h2 == q2.aux => q1.inst( c2 )
      case ( NegR( m1, r1 ), NegL( m2, r2 ), Neg( g ) ) if m1 == q1.aux && m2 == q2.aux =>
        evalCut( lctx, g,
          Subst( m2, f, q1 ).apply( r2, lctx2.up1_( q2.p ) ),
          Subst( m1, f, q2 ).apply( r1, lctx1.up1_( q1.p ) ) )
      case ( AndR( m1, r11, r12 ), AndL( m2, r2 ), And( g1, g2 ) ) if m1 == q1.aux && m2 == q2.aux =>
        evalCut( lctx, g2,
          Subst( m1, f, q2 ).apply( r12, lctx1.up2_( q1.p ) ),
          inst1(
            Subst( m2, f, q1 ).apply( r2, lctx2.up12_( q2.p ) ),
            g1, Subst( m1, f, q2 ).apply( r11, lctx1.up1_( q1.p ) ),
            lctx2, g1, g2 ) )
      case ( AndL( m1, r1 ), AndR( m2, r21, r22 ), BinConn( g1, g2 ) ) if m1 == q1.aux && m2 == q2.aux =>
        val r1_ = Subst( m1, f, q2 ).apply( r1, lctx1.up12_( q1.p ) )
        val r21_ = Subst( m2, f, q1 ).apply( r21, lctx2.up1_( q2.p ) )
        val r22_ = Subst( m2, f, q1 ).apply( r22, lctx2.up2_( q2.p ) )
        evalCut( lctx, g2, inst1( r1_, g1, r21_, lctx, g1, g2 ), r22_ )
      case ( AllR( m1, ev, r1 ), AllL( m2, t, r2 ), _ ) if m1 == q1.aux && m2 == q2.aux =>
        val inst = BetaReduction.betaNormalize( instantiate( f, t ) )
        evalCut( lctx, inst,
          Subst( m1, f, q2 ).apply( Substitution( ev -> t )( r1 ), lctx1.upS( inst ) ),
          Subst( m2, f, q1 ).apply( r2, lctx2.up1_( q2.p ) ) )
      case ( AllL( m1, t, r1 ), AllR( m2, ev, r2 ), _ ) if m1 == q1.aux && m2 == q2.aux =>
        val inst = BetaReduction.betaNormalize( instantiate( f, t ) )
        evalCut( lctx, inst,
          Subst( m1, f, q2 ).apply( r1, lctx1.up1_( q1.p ) ),
          Subst( m2, f, q1 ).apply( Substitution( ev -> t )( r2 ), lctx2.upS( inst ) ) )

      case ( _, _, _ ) if !q2.p.mainHyps.contains( q2.aux ) => inst( q2, f, q1, lctx2 )
      case ( _, _, _ ) if !q1.p.mainHyps.contains( q1.aux ) => inst( q1, f, q2, lctx1 )
      case _ => Cut( f, q1, q2 )
    }
  }
}

class NormalizerWithDebugging( implicit ctx: Maybe[Context] ) extends Normalizer[LocalCtx] {
  override def evalCut( c: Cut, lctx: LocalCtx ): LKt = {
    check( c, lctx )
    super.evalCut( c, lctx )
  }
}

object normalize {
  def apply( p: LKt ): LKt =
    new Normalizer[FakeLocalCtx]().normalize( p, FakeLocalCtx )
  def withDebug( p: LKt, lctx: LocalCtx )( implicit ctx: Maybe[Context] ): LKt =
    new NormalizerWithDebugging().normalize( p, lctx )
}
