package gapt.provers.congruence

import gapt.expr.util.subTerms
import gapt.expr.{ App, Atom, Eq, Expr }
import gapt.proofs.{ HOLClause, Sequent }
import gapt.provers.congruence.MutCC._

import scala.collection.mutable

object MutCC {
  case class Eqn( l: Int, r: Int, lr: Int )

  sealed trait Pending {
    def a: Int
    def b: Int
  }
  case class InputEq( a: Int, b: Int, ref: Int ) extends Pending
  case class PropagEq( e1: Eqn, e2: Eqn ) extends Pending {
    def a: Int = e1.lr
    def b: Int = e2.lr
  }
}

/**
 * Congruence closure implementation closely following [1]
 *
 * [1] R. Nieuwenhuis and A. Oliveras, Fast congruence closure and extensions, Information and Computation 205.4 (2007), 557-580.
 */
final class MutCC private (
    val n:       Int,
    val repr:    Array[Int],
    val klass:   Array[Vector[Int]],
    val use:     Array[Vector[Eqn]],
    val lookup:  mutable.Map[( Int, Int ), Eqn],
    val pending: mutable.ArrayStack[Pending],

    val parent: Array[Int],
    val reason: Array[Pending] ) {

  def this( n: Int ) =
    this(
      n,
      repr = ( 0 until n ).to[Array],
      klass = ( 0 until n ).view.map( i => Vector( i ): Vector[Int] ).to[Array],
      use = ( 0 until n ).view.map( _ => Vector.empty[Eqn]: Vector[Eqn] ).to[Array],
      lookup = mutable.AnyRefMap[( Int, Int ), Eqn](),
      pending = mutable.ArrayStack[Pending](),

      parent = ( 0 until n ).to[Array],
      reason = new Array[Pending]( n ) )

  override def clone(): MutCC =
    new MutCC(
      n,
      repr = repr.clone(),
      klass = klass.clone(),
      use = use.clone(),
      lookup = lookup.clone(),
      pending = pending.clone(),
      parent = parent.clone(),
      reason = reason.clone() )

  def resize( newN: Int ): MutCC =
    new MutCC(
      newN,
      repr = repr ++ ( n until newN ),
      klass = klass ++ ( n until newN ).view.map( i => Vector( i ) ),
      use = use ++ ( n until newN ).view.map( _ => Vector.empty[Eqn] ),
      lookup = lookup.clone(),
      pending = pending.clone(),
      parent = parent ++ ( n until newN ),
      reason = reason ++ ( n until newN ).view.map( _ => null ) )

  def addEqn( l: Int, r: Int, lr: Int ): Unit = addEqn( Eqn( l, r, lr ) )
  def addEqn( eqn: Eqn ): Unit = {
    val reprL = repr( eqn.l )
    val reprR = repr( eqn.r )
    lookup.get( ( reprL, reprR ) ) match {
      case Some( a ) =>
        merge( PropagEq( eqn, a ) )
      case None =>
        lookup( ( reprL, reprR ) ) = eqn
        use( reprL ) :+= eqn
        use( reprR ) :+= eqn
    }
    propagate()
  }

  def isEq( a: Int, b: Int ): Boolean = repr( a ) == repr( b )

  private def mergeLater( p: Pending ): Unit =
    if ( !isEq( p.a, p.b ) ) pending += p
  def merge( p: Pending ): Unit = {
    mergeLater( p )
    propagate()
  }
  def merge( a: Int, b: Int, ref: Int ): Unit = merge( InputEq( a, b, ref ) )

  def propagate(): Unit =
    while ( pending.nonEmpty ) {
      val p = pending.pop()
      val aRepr = repr( p.a )
      val bRepr = repr( p.b )

      if ( aRepr == bRepr )
        ()
      else if ( klass( aRepr ).size <= klass( bRepr ).size )
        propagateCore( aRepr, bRepr, p )
      else
        propagateCore( bRepr, aRepr, p )
    }

  private def reorient( a: Int ): Unit =
    parent( a ) match {
      case `a` =>
      case b =>
        reorient( b )
        parent( b ) = a
        reason( b ) = reason( a )
        reason( a ) = null
        parent( a ) = a
    }

  private def propagateCore( a: Int, b: Int, p: Pending ): Unit = {
    for ( Eqn( l, r, _ ) <- use( a ) )
      lookup.remove( ( repr( l ), repr( r ) ) )

    reorient( p.a )
    parent( p.a ) = p.b
    reason( p.a ) = p

    for ( a_ <- klass( a ) ) repr( a_ ) = b
    klass( b ) ++= klass( a )
    klass( a ) = Vector.empty

    for ( e1 @ Eqn( l, r, _ ) <- use( a ) )
      lookup.get( ( repr( l ), repr( r ) ) ) match {
        case Some( e2 ) =>
          mergeLater( PropagEq( e1, e2 ) )
        case None =>
          lookup( ( repr( l ), repr( r ) ) ) = e1
      }

    use( b ) ++= use( a )
    use( a ) = Vector.empty
  }

  def explain: Explainer = new Explainer
  class Explainer {
    val explainCache = mutable.Map[( Int, Int ), Set[Int]]()
    def apply( a: Int, b: Int ): Set[Int] = explain( a, b )
    def explain( a: Int, b: Int ): Set[Int] =
      if ( a == b ) Set.empty else explainCache.getOrElseUpdate( ( a, b ), {
        val c = nearestCommonAncestor( a, b )
        explainAlongPath( a, c ) union explainAlongPath( b, c )
      } )
    private def explainAlongPath( a: Int, b: Int ): Set[Int] =
      if ( a == b ) Set.empty else
        explainAlongPath( parent( a ), b ) union
          ( reason( a ) match {
            case InputEq( _, _, ref ) =>
              Set( ref )
            case PropagEq( e1, e2 ) =>
              explain( e1.l, e2.l ) union explain( e1.r, e2.r )
          } )
    def ancestors( a: Int ): List[Int] =
      a :: ( parent( a ) match { case `a` => Nil case b => ancestors( b ) } )
    private def nearestCommonAncestor( a: Int, b: Int ): Int = {
      val as = ancestors( a )
      val bs = ancestors( b )
      as.find( as.toSet intersect bs.toSet ).get
    }
  }

}

class CC( mutCC0: MutCC, val termToIdx: Map[Expr, Int], val idxToTerm: Map[Int, Expr] ) {
  def mkMut(): MutCC = mutCC0.clone()
  def merge( eqns: Iterable[Expr] ): CC = {
    val cc = mkMut()
    for ( eqn @ Eq( a, b ) <- eqns ) cc.merge( termToIdx( a ), termToIdx( b ), termToIdx( eqn ) )
    new CC( cc, termToIdx, idxToTerm )
  }
  def intern( exprs: Iterable[Expr] ): CC = {
    val subExprs = exprs.flatMap( subTerms( _ ) ).toSet
    val tti = termToIdx ++ subExprs.diff( termToIdx.keySet ).zip( termToIdx.size until Int.MaxValue )
    val cc = mutCC0.resize( tti.size )
    for ( e @ App( a, b ) <- subExprs ) cc.addEqn( tti( a ), tti( b ), tti( e ) )
    new CC( cc, tti, tti.map( _.swap ) )
  }
  def internAndMerge( exprs: Iterable[Expr] ): CC =
    intern( exprs ).merge( exprs )

  def isEq( a: Expr, b: Expr ): Boolean =
    mutCC0.isEq( termToIdx( a ), termToIdx( b ) )

  def explain( clause: HOLClause ): Option[HOLClause] = {
    val expl = mutCC0.explain
    val cores =
      clause.succedent.collect {
        case e @ Eq( t, s ) if mutCC0.isEq( termToIdx( t ), termToIdx( s ) ) =>
          val es = expl( termToIdx( t ), termToIdx( s ) )
          ( es.size, () => Sequent( es.map( idxToTerm( _ ).asInstanceOf[Atom] ).toVector, Vector( e ) ) )
      } ++ {
        val reprClause = clause.map( termToIdx.mapValues( mutCC0.repr ) )
        reprClause.antecedent.toSet.intersect( reprClause.succedent.toSet ).map { r =>
          val i = reprClause.indexOfInAnt( r )
          val j = reprClause.indexOfInSuc( r )
          val es = expl( termToIdx( clause( i ) ), termToIdx( clause( j ) ) )
          ( es.size, () =>
            Sequent(
              ( es.map( idxToTerm( _ ).asInstanceOf[Atom] ) + clause( i ) ).toVector,
              Vector( clause( j ) ) ) )
        }
      }
    if ( cores.isEmpty ) None else Some( cores.minBy( _._1 )._2() )
  }
  def mergeAndExplain( clause: HOLClause ): Option[HOLClause] =
    merge( clause.antecedent ).explain( clause )
}

object CC {
  def apply(): CC = new CC( new MutCC( 0 ), Map(), Map() )

  def isValid( clause: HOLClause ): Option[HOLClause] =
    CC().intern( clause.elements ).mergeAndExplain( clause )
}

