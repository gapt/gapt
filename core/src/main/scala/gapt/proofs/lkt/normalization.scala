package gapt.proofs.lkt

import gapt.expr._
import gapt.expr.hol.{ containsQuantifierOnLogicalLevel, instantiate, isAtom }
import gapt.proofs.Context
import gapt.proofs.lk.LKProof
import gapt.provers.simp.{ QPropSimpProc, SimpLemmas, Simplifier }
import gapt.utils.Maybe

class Normalizer[LC <: ALCtx[LC]]( skipCut: Formula => Boolean ) {
  protected def doCheck( p: LKt, lctx: LC ): Unit = ()

  case class ProofSubst( hyp: Hyp, byF: Formula, by: Bound1 ) {
    def apply( bnd: Bound1, lctx: B1[LC] ): Bound1 =
      if ( bnd.aux == hyp ) bnd
      else if ( !by.freeHyps( bnd.aux ) ) Bound1( bnd.aux, apply( bnd.p, lctx( bnd.aux ) ) )
      else apply( bnd.rename( by.freeHyps ), lctx )
    def apply( bnd: Bound2, lctx: B2[LC] ): Bound2 =
      if ( bnd.aux1 == hyp || bnd.aux2 == hyp ) bnd
      else if ( !by.freeHyps( bnd.aux1 ) && !by.freeHyps( bnd.aux2 ) )
        Bound2( bnd.aux1, bnd.aux2, apply( bnd.p, lctx( bnd.aux1, bnd.aux2 ) ) )
      else apply( bnd.rename( by.freeHyps ), lctx )
    def apply( bnd: BoundN, lctx: BN[LC] ): BoundN =
      if ( bnd.auxs.contains( hyp ) ) bnd
      else if ( by.freeHyps.intersect( bnd.auxs.toSet ).isEmpty )
        BoundN( bnd.auxs, apply( bnd.p, lctx( bnd.auxs ) ) )
      else apply( bnd.rename( by.freeHyps ), lctx )

    def apply( p: LKt, lctx: LC ): LKt = p match {
      case _ if !p.freeHyps( hyp ) => p
      case Cut( f, q1, q2 )        => Cut.f( f, apply( q1, lctx.up1_( p ) ), apply( q2, lctx.up2_( p ) ) )
      case Ax( m1, m2 ) =>
        if ( hyp == m1 ) by.inst( m2 )
        else if ( hyp == m2 ) by.inst( m1 )
        else p
      case Rfl( main ) if main != hyp     => p
      case TopR( cohyp ) if cohyp != hyp  => p
      case NegR( main, q ) if main != hyp => NegR.f( main, apply( q, lctx.up1_( p ) ) )
      case NegL( main, q ) if main != hyp => NegL.f( main, apply( q, lctx.up1_( p ) ) )
      case AndR( main, q1, q2 ) if main != hyp =>
        AndR.f( main, apply( q1, lctx.up1_( p ) ), apply( q2, lctx.up2_( p ) ) )
      case AndL( main, q ) if main != hyp       => AndL.f( main, apply( q, lctx.up12_( p ) ) )
      case AllL( main, term, q ) if main != hyp => AllL.f( main, term, apply( q, lctx.up1_( p ) ) )
      case AllR( main, ev, q ) if main != hyp =>
        if ( !by.p.freeVars( ev ) ) AllR.f( main, ev, apply( q, lctx.up1_( p ) ) ) else {
          val ev_ = rename( ev, by.p.freeVars union p.freeVars )
          apply( AllR.f( main, ev_, Substitution( ev -> ev_ )( q ) ), lctx )
        }
      case Eql( main, eq, ltr, rwCtx, q ) if main != hyp && eq != hyp =>
        Eql.f( main, eq, ltr, rwCtx, apply( q, lctx.up1_( p ) ) )
      case AllSk( main, term, skDef, q ) if main != hyp =>
        AllSk.f( main, term, skDef, apply( q, lctx.up1_( p ) ) )
      case Def( main, f, q ) if main != hyp =>
        Def.f( main, f, apply( q, lctx.up1_( p ) ) )
      case Ind( main, f, t, cases ) if main != hyp =>
        Ind( main, f, t, for ( ( c, n ) <- cases.zipWithIndex ) yield c.copy( q = apply( c.q, lctx.upn_( p, n ) ) ) )
      case Link( mains, _ ) if !mains.contains( hyp ) => p
      case _ =>
        if ( hyp.inSuc ) evalCut( lctx, byF, Bound1( hyp, p ), by )
        else evalCut( lctx, byF, by, Bound1( hyp, p ) )
    }
  }

  def normalize( bnd: Bound1, lctx: LC ): Bound1 = Bound1( bnd.aux, normalize( bnd.p, lctx ) )
  def normalize( bnd: Bound2, lctx: LC ): Bound2 = Bound2( bnd.aux1, bnd.aux2, normalize( bnd.p, lctx ) )
  def normalize( bnd: BoundN, lctx: LC ): BoundN = BoundN( bnd.auxs, normalize( bnd.p, lctx ) )
  def normalize( p: LKt, lctx: LC ): LKt = p match {
    case _ if !p.hasCuts => p
    case Cut( f, q1, q2 ) =>
      evalCut( lctx, f, normalize( q1, lctx.up1( p ) ), normalize( q2, lctx.up2( p ) ) )
    case Ax( _, _ ) | Rfl( _ ) | TopR( _ ) => p
    case NegR( main, q )                   => NegR.f( main, normalize( q, lctx.up1( p ) ) )
    case NegL( main, q )                   => NegL.f( main, normalize( q, lctx.up1( p ) ) )
    case AndR( main, q1, q2 )              => AndR.f( main, normalize( q1, lctx.up1( p ) ), normalize( q2, lctx.up2( p ) ) )
    case AndL( main, q )                   => AndL.f( main, normalize( q, lctx.up1( p ) ) )
    case AllL( main, term, q )             => AllL.f( main, term, normalize( q, lctx.up1( p ) ) )
    case AllR( main, ev, q )               => AllR.f( main, ev, normalize( q, lctx.up1( p ) ) )
    case Eql( main, eq, ltr, rwCtx, q )    => Eql.f( main, eq, ltr, rwCtx, normalize( q, lctx.up1( p ) ) )
    case AllSk( main, term, skDef, q )     => AllSk.f( main, term, skDef, normalize( q, lctx.up1( p ) ) )
    case Def( main, f, q )                 => Def.f( main, f, normalize( q, lctx.up1( p ) ) )
    case Ind( main, f, t, cases ) =>
      Ind( main, f, t, for ( ( c, i ) <- cases.zipWithIndex )
        yield c.copy( q = normalize( c.q, lctx.upn( p, i ) ) ) )
    case Link( _, _ ) => p
  }

  def normalizeWithInduction( p: LKt, lctx: LC, simpAdapter: SimpAdapter )( implicit ctx: Context ): LKt = {
    val p2 = normalize( p, lctx )
    unfoldInduction( p2, simpAdapter ) match {
      case Some( p3 ) =>
        doCheck( p3, lctx )
        normalizeWithInduction( p3, lctx, simpAdapter )
      case None =>
        p2
    }
  }

  protected def inst( q: Bound1, byF: Formula, by: Bound1, lctx: LC ): LKt = ProofSubst( q.aux, byF, by ).apply( q.p, lctx )
  protected def inst1( q: Bound2, byF: Formula, by: Bound1, lctx: LC, g1: Formula, g2: Formula ): Bound1 =
    ProofSubst( q.aux1, byF, by ).apply( Bound1( q.aux2, q.p ), lctx.upS( g1 )( q.aux1 ).upS( g2 ) )

  def evalCut( lctx: LC, f: Formula, q1: Bound1, q2: Bound1 ): LKt =
    evalCut( Cut( f, q1, q2 ), lctx )

  def evalCut( c: Cut, lctx: LC ): LKt = {
    doCheck( c, lctx )
    val Cut( f, q1, q2 ) = c
    if ( q1.isConst ) return q1.p
    if ( q2.isConst ) return q2.p
    if ( skipCut( f ) ) return c
    if ( q2.freeHyps( q1.aux ) ) return evalCut( Cut( f, q1.rename( q2.freeHyps ), q2 ), lctx )
    if ( q1.freeHyps( q2.aux ) ) return evalCut( Cut( f, q1, q2.rename( q1.freeHyps ) ), lctx )
    val lctx1 = lctx.up1( c )
    val lctx2 = lctx.up2( c )
    ( q1.p, q2.p, f ) match {
      case ( Ax( h1, c1 ), _, _ ) if c1 == q1.aux => q2.inst( h1 )
      case ( _, Ax( h2, c2 ), _ ) if h2 == q2.aux => q1.inst( c2 )
      case ( NegR( m1, r1 ), NegL( m2, r2 ), Neg( g ) ) if m1 == q1.aux && m2 == q2.aux =>
        evalCut( lctx, g,
          ProofSubst( m2, f, q1 ).apply( r2, lctx2.up1_( q2.p ) ),
          ProofSubst( m1, f, q2 ).apply( r1, lctx1.up1_( q1.p ) ) )
      case ( AndR( m1, r11, r12 ), AndL( m2, r2 ), And( g1, g2 ) ) if m1 == q1.aux && m2 == q2.aux =>
        evalCut( lctx, g2,
          ProofSubst( m1, f, q2 ).apply( r12, lctx1.up2_( q1.p ) ),
          inst1(
            ProofSubst( m2, f, q1 ).apply( r2, lctx2.up12_( q2.p ) ),
            g1, ProofSubst( m1, f, q2 ).apply( r11, lctx1.up1_( q1.p ) ),
            lctx2, g1, g2 ) )
      case ( AndL( m1, r1 ), AndR( m2, r21, r22 ), BinConn( g1, g2 ) ) if m1 == q1.aux && m2 == q2.aux =>
        val r1_ = ProofSubst( m1, f, q2 ).apply( r1, lctx1.up12_( q1.p ) )
        val r21_ = ProofSubst( m2, f, q1 ).apply( r21, lctx2.up1_( q2.p ) )
        val r22_ = ProofSubst( m2, f, q1 ).apply( r22, lctx2.up2_( q2.p ) )
        evalCut( lctx, g2, inst1( r1_, g1, r21_, lctx, g1, g2 ), r22_ )
      case ( AllR( m1, ev, r1 ), AllL( m2, t, r2 ), _ ) if m1 == q1.aux && m2 == q2.aux =>
        val inst = BetaReduction.betaNormalize( instantiate( f, t ) )
        evalCut( lctx, inst,
          ProofSubst( m1, f, q2 ).apply( Substitution( ev -> t )( r1 ), lctx1.upS( inst ) ),
          ProofSubst( m2, f, q1 ).apply( r2, lctx2.up1_( q2.p ) ) )
      case ( AllL( m1, t, r1 ), AllR( m2, ev, r2 ), _ ) if m1 == q1.aux && m2 == q2.aux =>
        val inst = BetaReduction.betaNormalize( instantiate( f, t ) )
        evalCut( lctx, inst,
          ProofSubst( m1, f, q2 ).apply( r1, lctx1.up1_( q1.p ) ),
          ProofSubst( m2, f, q1 ).apply( Substitution( ev -> t )( r2 ), lctx2.upS( inst ) ) )

      case ( _, _, _ ) if !q2.p.mainHyps.contains( q2.aux ) => inst( q2, f, q1, lctx2 )
      case ( _, _, _ ) if !q1.p.mainHyps.contains( q1.aux ) => inst( q1, f, q2, lctx1 )
      case _ => Cut( f, q1, q2 )
    }
  }
}

class NormalizerWithDebugging( implicit ctx: Maybe[Context] ) extends Normalizer[LocalCtx]( skipCut = _ => false ) {
  override def doCheck( p: LKt, lctx: LocalCtx ): Unit = check( p, lctx )
}

class normalize {
  def lk( p: LKProof, skipCut: Formula => Boolean = _ => false ): LKProof = {
    val ( q, lctx ) = LKToLKt( p )
    LKtToLK( apply( q, skipCut ), lctx )
  }
  def apply( p: LKt, skipCut: Formula => Boolean = _ => false ): LKt =
    new Normalizer[FakeLocalCtx]( skipCut ) {}.normalize( p, FakeLocalCtx )
  def withDebug( p: LKProof )( implicit ctx: Maybe[Context] ): LKt = {
    val ( t, lctx ) = LKToLKt( p )
    withDebug( t, lctx )
  }
  def withDebug( p: LKt, lctx: LocalCtx )( implicit ctx: Maybe[Context] ): LKt =
    new NormalizerWithDebugging().normalize( p, lctx )

  def induction( p: LKt, lctx: LocalCtx, useSimp: Boolean = true, debugging: Boolean = false,
                 skipCut: Formula => Boolean = _ => false )( implicit ctx: Context ): LKt = {
    val simpAdapter = if ( !useSimp ) NoopSimpAdapter else SimplifierSimpAdapter(
      Simplifier( SimpLemmas.collectFromAnt( lctx.toSequent ).toSeq :+ QPropSimpProc ), lctx )
    if ( debugging )
      new NormalizerWithDebugging().normalizeWithInduction( p, lctx, simpAdapter )
    else
      new Normalizer[FakeLocalCtx]( skipCut ) {}.
        normalizeWithInduction( p, FakeLocalCtx, simpAdapter )
  }
  def inductionWithDebug( p: LKProof )( implicit ctx: Context ): LKt = {
    val ( lkt, lctx ) = LKToLKt( p )
    induction( lkt, lctx )
  }
}
object normalize extends normalize
object normalizeLKt extends normalize
