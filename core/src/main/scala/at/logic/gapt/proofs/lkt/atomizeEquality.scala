package at.logic.gapt.proofs.lkt

import at.logic.gapt.expr._

object atomizeEquality {

  def apply( b: Bound1, lctx: LocalCtx ): Bound1 = b.copy( p = apply( b.p, lctx ) )
  def apply( b: Bound2, lctx: LocalCtx ): Bound2 = b.copy( p = apply( b.p, lctx ) )
  def apply( b: BoundN, lctx: LocalCtx ): BoundN = b.copy( p = apply( b.p, lctx ) )

  def apply( p: LKt, lctx: LocalCtx ): LKt = p match {
    case Cut( f, q1, q2 ) =>
      Cut( f, apply( q1, lctx.up1( p ) ), apply( q2, lctx.up2( p ) ) )
    case Ax( _, _ ) | Rfl( _ ) | TopR( _ ) | Link( _, _ ) => p
    case NegR( main, q ) =>
      NegR( main, apply( q, lctx.up1( p ) ) )
    case NegL( main, q ) =>
      NegL( main, apply( q, lctx.up1( p ) ) )
    case AndR( main, q1, q2 ) =>
      AndR( main, apply( q1, lctx.up1( p ) ), apply( q2, lctx.up2( p ) ) )
    case AndL( main, q ) =>
      AndL( main, apply( q, lctx.up1( p ) ) )
    case AllL( main, term, q ) =>
      AllL( main, term, apply( q, lctx.up1( p ) ) )
    case AllR( main, ev, q ) =>
      AllR( main, ev, apply( q, lctx.up1( p ) ) )
    case Eql( main, eq, ltr, rwCtx @ Abs( _, _: Atom ), q ) =>
      Eql( main, eq, ltr, rwCtx, apply( q, lctx.up1( p ) ) )
    case Eql( main, eq, ltr, rwCtx, q ) if main.inAnt =>
      val aux = Set( main, eq ).fresh( !main.polarity )
      val cutf = lctx.up1( p )( q.aux )
      val sim = simulate( rwCtx, ltr, eq, main, aux )
      Cut( cutf, Bound1( aux, sim ), apply( q, lctx.up1( p ) ) )
    case Eql( main, eq, ltr, rwCtx, q ) if main.inSuc =>
      val aux = Set( main, eq ).fresh( !main.polarity )
      val cutf = lctx.up1( p )( q.aux )
      val sim = simulate( rwCtx, !ltr, eq, aux, main )
      Cut( cutf, apply( q, lctx.up1( p ) ), Bound1( aux, sim ) )
    case AllSk( main, term, skDef, q ) =>
      AllSk( main, term, skDef, apply( q, lctx.up1( p ) ) )
    case Def( main, f, q ) =>
      Def( main, f, apply( q, lctx.up1( p ) ) )
    case Ind( main, f, term, cases ) =>
      Ind( main, f, term, cases.zipWithIndex.map { case ( c, i ) => c.copy( q = apply( c.q, lctx.upn( p, i ) ) ) } )
  }

  /**
   * Produces a proof of
   * eq: l=r, left: rwCtx(l) :- right: rwCtx(r)
   */
  def simulate( rwCtx: Expr, ltr: Boolean, eq: Hyp, left: Hyp, right: Hyp ): LKt =
    rwCtx match {
      case Abs( x, phi ) if !freeVariables( phi ).contains( x ) =>
        Ax( left, right )
      case Abs( x, Neg( phi ) ) =>
        val List( left_, right_ ) =
          Set( eq, left, right ).freshSameSide( List( left, right ) )
        NegL( left, Bound1(
          right_,
          NegR( right, Bound1(
            left_,
            simulate( Abs( x, phi ), !ltr, eq, left_, right_ ) ) ) ) )
      case Abs( x, And( phi, psi ) ) =>
        val List( left1, left2, right1, right2 ) =
          Set( eq, left, right ).freshSameSide( List( left, left, right, right ) )
        AndL( left, Bound2( left1, left2,
          AndR(
            right,
            Bound1( right1, simulate( Abs( x, phi ), ltr, eq, left1, right1 ) ),
            Bound1( right2, simulate( Abs( x, psi ), ltr, eq, left2, right2 ) ) ) ) )
      case Abs( x, Or( phi, psi ) ) =>
        val List( left1, left2, right1, right2 ) =
          Set( eq, left, right ).freshSameSide( List( left, left, right, right ) )
        AndL( right, Bound2( right1, right2,
          AndR(
            left,
            Bound1( left1, simulate( Abs( x, phi ), ltr, eq, left1, right1 ) ),
            Bound1( left2, simulate( Abs( x, psi ), ltr, eq, left2, right2 ) ) ) ) )
      case Abs( x, Imp( phi, psi ) ) =>
        val List( left1, left2, right1, right2 ) =
          Set( eq, left, right ).freshSameSide( List( left, left, right, right ) )
        AndL( right, Bound2( left1, right2,
          AndR(
            left,
            Bound1( right1, simulate( Abs( x, phi ), !ltr, eq, left1, right1 ) ),
            Bound1( left2, simulate( Abs( x, psi ), ltr, eq, left2, right2 ) ) ) ) )
      case Abs( x, All( y, phi ) ) =>
        assert( x != y )
        val List( left_, right_ ) =
          Set( eq, left, right ).freshSameSide( List( left, right ) )
        AllR( right, y, Bound1(
          right_,
          AllL( left, y, Bound1(
            left_,
            simulate( Abs( x, phi ), ltr, eq, left_, right_ ) ) ) ) )
      case Abs( x, Ex( y, phi ) ) =>
        assert( x != y )
        val List( left_, right_ ) =
          Set( eq, left, right ).freshSameSide( List( left, right ) )
        AllR( left, y, Bound1(
          left_,
          AllL( right, y, Bound1(
            right_,
            simulate( Abs( x, phi ), ltr, eq, left_, right_ ) ) ) ) )
      case _ =>
        Eql( left, eq, ltr, rwCtx, Bound1( left, Ax( left, right ) ) )
    }

}
