package at.logic.gapt.proofs.lkt

import at.logic.gapt.expr.{ All, BetaReduction, Eq, Expr, Formula, Ty, Var, freeVariables, rename }

import scala.collection.mutable

class makeEqualityExplicit( debugging: Boolean ) extends FreshHyp {
  // (replacement context, ltr) |-> (hyp, eqAxiom)
  val rwrHyps = mutable.Map[( Expr, Boolean ), ( Hyp, Formula )]()

  // ty |-> (hyp, rflAxiom)
  val reflHyps = mutable.Map[Ty, ( Hyp, Formula )]()

  def effectiveLCtx( lctx: LocalCtx ): LocalCtx =
    lctx.updated( rwrHyps.values ).updated( reflHyps.values )

  def apply( p: LKt, lctx: LocalCtx ): ( LKt, LocalCtx ) = {
    markUsed( p )
    val q = go( p, lctx )
    q -> effectiveLCtx( lctx )
  }

  def go( b: Bound1, lctx: LocalCtx ): Bound1 = b.copy( p = go( b.p, lctx ) )
  def go( b: Bound2, lctx: LocalCtx ): Bound2 = b.copy( p = go( b.p, lctx ) )
  def go( b: BoundN, lctx: LocalCtx ): BoundN = b.copy( p = go( b.p, lctx ) )
  def go( p: LKt, lctx: LocalCtx ): LKt = {
    val result = p match {
      case Cut( f, q1, q2 )                      => Cut( f, go( q1, lctx.up1( p ) ), go( q2, lctx.up2( p ) ) )
      case Ax( _, _ ) | TopR( _ ) | Link( _, _ ) => p
      case Rfl( main ) =>
        val Eq( t, _ ) = lctx( main )
        val rflHyp = reflHyps.getOrElseUpdate( t.ty, {
          val x = Var( "x", t.ty )
          ( freshAnt(), All( x, x === x ) )
        } )._1
        AllL( rflHyp, t, Bound1( rflHyp, Ax( rflHyp, main ) ) )
      case NegR( main, q )       => NegR( main, go( q, lctx.up1( p ) ) )
      case NegL( main, q )       => NegL( main, go( q, lctx.up1( p ) ) )
      case AndR( main, q1, q2 )  => AndR( main, go( q1, lctx.up1( p ) ), go( q2, lctx.up2( p ) ) )
      case AndL( main, q )       => AndL( main, go( q, lctx.up1( p ) ) )
      case AllL( main, term, q ) => AllL( main, term, go( q, lctx.up1( p ) ) )
      case AllR( main, ev, q )   => AllR( main, ev, go( q, lctx.up1( p ) ) )
      case Eql( main, eq, ltr, rwCtx, q ) =>
        val Eq( l, r ) = lctx( eq )
        val extraVars = freeVariables( rwCtx ).toList
        val effLtr = ltr == main.inAnt
        val rwrHyp = rwrHyps.getOrElseUpdate( ( rwCtx, effLtr ), {
          val nameGen = rename.awayFrom( extraVars )
          val x = nameGen.fresh( Var( "x", l.ty ) )
          val y = nameGen.fresh( Var( "y", l.ty ) )
          val ax = All.Block( extraVars :+ x :+ y, ( x === y ) --> BetaReduction.betaNormalize(
            if ( effLtr ) rwCtx( x ) --> rwCtx( y ) else rwCtx( y ) --> rwCtx( x ) ) )
          ( freshAnt(), ax )
        } )._1
        val aux = freshSuc()
        AllLBlock( rwrHyp, extraVars :+ l :+ r, Bound1( rwrHyp, AndR( rwrHyp, Bound1( aux, Ax( eq, aux ) ),
          Bound1( rwrHyp, AndR(
            rwrHyp,
            Bound1( aux, if ( main.inAnt ) Ax( main, aux ) else go( q, lctx.up1( p ) ).inst( aux ) ),
            Bound1( rwrHyp, if ( main.inSuc ) Ax( rwrHyp, main ) else go( q, lctx.up1( p ) ).inst( rwrHyp ) ) ) ) ) ) )
      case AllSk( main, term, skDef, q ) => AllSk( main, term, skDef, go( q, lctx.up1( p ) ) )
      case Def( main, f, q )             => Def( main, f, go( q, lctx.up1( p ) ) )
      case Ind( main, f, term, cases ) =>
        Ind( main, f, term, cases.zipWithIndex.map { case ( c, i ) => c.copy( q = go( c.q, lctx.upn( p, i ) ) ) } )
    }
    if ( debugging ) check( result, effectiveLCtx( lctx ) )
    result
  }

}

object makeEqualityExplicit {
  def apply( p: LKt, lctx: LocalCtx, debugging: Boolean = false ): ( LKt, LocalCtx ) =
    new makeEqualityExplicit( debugging ).apply( p, lctx )
}