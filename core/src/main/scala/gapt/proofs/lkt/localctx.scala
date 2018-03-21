package gapt.proofs.lkt

import gapt.expr._
import gapt.expr.hol.instantiate
import gapt.proofs.{ HOLSequent, Sequent }

object BinConn {
  def unapply( f: Formula ): Option[( Formula, Formula )] =
    f match {
      case And( g1, g2 ) => Some( g1, g2 )
      case Or( g1, g2 )  => Some( g1, g2 )
      case Imp( g1, g2 ) => Some( g1, g2 )
      case _             => None
    }
}

case class LocalCtx( hyps: Map[Hyp, Formula], subst: Substitution ) extends ALCtx[LocalCtx] {
  import ExprSubstWithβ._

  def toSequent: HOLSequent = Sequent { for ( ( h, f ) <- hyps ) yield f -> h.polarity }

  def updated( hyp: Hyp, f: Formula ): LocalCtx = copy( hyps.updated( hyp, f ) )
  def updated( hs: Iterable[( Hyp, Formula )] ): LocalCtx = copy( hyps = hyps ++ hs )
  def renamed( a: Hyp, b: Hyp ): LocalCtx = copy( hyps = hyps - a + ( b -> hyps( a ) ) )
  def apply( hyp: Hyp ) = hyps( hyp )
  def formulas = hyps.values
  def freeVars = freeVariables( hyps.values )

  override def toString =
    hyps.toSeq.sortBy( _._1.idx ).map( p => s"${p._1} -> ${p._2}" ).mkString( "\n" ) + "\n" + subst

  def up( f: Formula ): LC1 = h => updated( h, f )
  def up( f1: Formula, f2: Formula ): LC2 = ( h1, h2 ) => updated( h1, f1 ).updated( h2, f2 )
  def up( fs: List[Formula] ): LCN = hs => hs.zip( fs ).foldLeft( this )( ( lctx, h ) => lctx.updated( h._1, h._2 ) )

  def upS( f: Formula ): LC1 = up( subst( f ) )
  def upS( f1: Formula, f2: Formula ): LC2 = up( subst( f1 ), subst( f2 ) )

  def up1_( p: LKt ): LC1 = ( p: @unchecked ) match {
    case Cut( f, _, _ )     => up( subst( f ) )
    case AndR( main, _, _ ) => up( hyps( main ) match { case BinConn( g, _ ) => g } )
    case NegR( main, _ )    => up( hyps( main ) match { case Neg( g ) => g } )
    case NegL( main, _ )    => up( hyps( main ) match { case Neg( g ) => g } )
    case p: Eql =>
      up( BetaReduction.betaNormalize( subst( p.rwCtx ).apply( eqRhs( p ) ).asInstanceOf[Formula] ) )
    case p: AllL => up( BetaReduction.betaNormalize( instantiate( hyps( p.main ), subst( p.term ) ) ) )
    case p: AllR =>
      if ( subst.domain( p.ev ) ) {
        copy( subst = Substitution( subst.map - p.ev, subst.typeMap ) ).up1_( p )
      } else {
        val ev = rename( p.ev, subst.range union subst.domain union freeVars )
        copy( subst = subst compose Substitution( p.ev -> ev ) ).
          up( instantiate( hyps( p.main ), ev ) )
      }
    case AllSk( main, term, _, _ ) => up( instantiate( hyps( main ), subst( term ) ) )
    case Def( _, f, _ )            => up( subst( f ) )
  }
  def up12_( p: LKt ): LC2 = ( p: @unchecked ) match {
    case AndL( main, _ ) => hyps( main ) match { case BinConn( f, g ) => up( f, g ) }
  }
  def up2_( p: LKt ): LC1 = ( p: @unchecked ) match {
    case c: Cut  => up( BetaReduction.betaNormalize( subst( c.f ) ) )
    case p: AndR => up( hyps( p.main ) match { case BinConn( _, g ) => g } )
  }
  def upn_( p: LKt, n: Int ): LCN = ( p: @unchecked ) match {
    case p @ Ind( _, f0, _, cases ) =>
      val f = subst( f0 )
      val c = cases( n )
      if ( c.evs.toSet.intersect( subst.domain ).nonEmpty ) {
        copy( subst = Substitution( subst.map -- c.evs, subst.typeMap ) ).upn_( p, n )
      } else {
        val evs = c.evs.map( rename( c.evs, subst.range union subst.domain union freeVars ) )
        val ihs = for ( ev <- evs if ev.ty == p.indTy )
          yield Substitution( f.variable -> ev )( f.term ).asInstanceOf[Formula]
        val goal = Substitution( f.variable -> c.ctr( evs ) )( f.term ).asInstanceOf[Formula]
        copy( subst = subst compose Substitution( c.evs zip evs ) ).up( goal +: ihs )
      }
  }

  def eqLhs( p: Eql ) = hyps( p.eq ) match { case Eq( t, s ) => if ( p.ltr ) t else s }
  def eqRhs( p: Eql ) = hyps( p.eq ) match { case Eq( t, s ) => if ( p.ltr ) s else t }
}

trait B1[LC <: ALCtx[LC]] { def apply( h: Hyp ): LC }
trait B2[LC <: ALCtx[LC]] { def apply( h1: Hyp, h2: Hyp ): LC }
trait BN[LC <: ALCtx[LC]] { def apply( hs: List[Hyp] ): LC }

trait ALCtx[LC <: ALCtx[LC]] {
  type LC1 = B1[LC]
  type LC2 = B2[LC]
  type LCN = BN[LC]

  def up1_( p: LKt ): LC1
  def up12_( p: LKt ): LC2
  def up2_( p: LKt ): LC1
  def upn_( p: LKt, n: Int ): LCN
  def renamed( a: Hyp, b: Hyp ): LC

  def up1( p: LKt ): LC = ( p: @unchecked ) match {
    case Cut( _, q1, _ )      => up1_( p )( q1.aux )
    case NegR( _, q )         => up1_( p )( q.aux )
    case NegL( _, q )         => up1_( p )( q.aux )
    case AndR( _, q1, _ )     => up1_( p )( q1.aux )
    case AndL( _, q )         => up12_( p )( q.aux1, q.aux2 )
    case AllL( _, _, q )      => up1_( p )( q.aux )
    case AllR( _, _, q )      => up1_( p )( q.aux )
    case Eql( _, _, _, _, q ) => up1_( p )( q.aux )
    case AllSk( _, _, _, q )  => up1_( p )( q.aux )
    case Def( _, _, q )       => up1_( p )( q.aux )
  }
  def up2( p: LKt ): LC = ( p: @unchecked ) match {
    case Cut( _, _, q2 )  => up2_( p )( q2.aux )
    case AndR( _, _, q2 ) => up2_( p )( q2.aux )
  }
  def upn( p: LKt, n: Int ): LC = ( p: @unchecked ) match {
    case Ind( _, _, _, cases ) => upn_( p, n )( cases( n ).q.auxs )
  }

  def upS( f: Formula ): LC1
  def upS( f1: Formula, f2: Formula ): LC2
}
class FakeLocalCtx extends ALCtx[FakeLocalCtx] {
  def up1_( p: LKt ): LC1 = upS( null )
  def up12_( p: LKt ): LC2 = upS( null, null )
  def up2_( p: LKt ): LC1 = up1_( p )
  def upn_( p: LKt, n: Int ): LCN = _ => this
  def renamed( a: Hyp, b: Hyp ): FakeLocalCtx = this
  def upS( f: Formula ): LC1 = _ => this
  def upS( f1: Formula, f2: Formula ): LC2 = ( _, _ ) => this
}
case object FakeLocalCtx extends FakeLocalCtx
