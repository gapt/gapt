package at.logic.gapt.provers.congruence
import CongruenceClosure._
import at.logic.gapt.expr._
import at.logic.gapt.proofs.congruence._
import cats.syntax.traverse._
import cats.instances.list._
import cats.instances.option._

import scala.collection.mutable

class CongruenceClosure private (
    val equalToRepr: Map[Expr, CongruenceProof],
    val parents:     Map[Expr, Set[Expr]] ) {
  if ( true ) {
    val rs = representatives
    for ( ( a, p ) <- equalToRepr ) {
      require( a == p.lhs )
      require( rs.contains( p.rhs ) )
      if ( rs.contains( a ) ) {
        require( p.lhs == p.rhs )
      }
    }
    for ( ( a, ps ) <- parents ) {
      require( rs.contains( a ) )
      for ( p <- ps ) require( rs.contains( p ) )
    }
  }

  def findRepr( e: Expr ): Expr =
    equalToRepr( e ).rhs

  def representatives: Set[Expr] =
    Set() ++ equalToRepr.mapValues( _.rhs ).values

  def internalize( e: Expr ): CongruenceClosure =
    if ( equalToRepr.contains( e ) ) this else {
      var c = this

      def int( e: Expr, par: Option[Expr] ): Unit =
        c.equalToRepr.get( e ) match {
          case Some( e_ ) =>
            for ( p <- par ) c = c.addParent( e_.rhs, c.findRepr( p ) )
            c = c.propagate( e_.rhs )
          case None =>
            c = c.addTerm( e, par.map( c.findRepr ) )
            val Apps( _, sts ) = e
            for ( st <- sts ) int( st, Some( e ) )
        }

      int( e, None )
      c
    }

  def equivalenceClass( e: Expr ): Iterable[Expr] = {
    val ei = findRepr( e )
    for ( ( a, p ) <- equalToRepr if p.rhs == ei ) yield a
  }

  def isEquivalent( a: Expr, b: Expr ): Boolean = {
    val c = internalize( a ).internalize( b )
    c.findRepr( a ) == c.findRepr( b )
  }

  def getEqvProof( a: Expr, b: Expr ): Option[CongruenceProof] = {
    val c = internalize( a ).internalize( b )
    for {
      p1 <- c.equalToRepr.get( a )
      p2 <- c.equalToRepr.get( b )
      if p1.rhs == p2.rhs
    } yield p1 * p2.inv
  }

  def isEquivalent( eqn: Equation ): Boolean =
    isEquivalent( eqn._1, eqn._2 )

  private def union( p0: CongruenceProof ): CongruenceClosure = {
    val p = equalToRepr( p0.lhs ).inv * p0 * equalToRepr( p0.rhs )
    val ( a, b ) = ( p.lhs, p.rhs )
    if ( a == b ) return this
    // I am aware that this is the shittiest union-find ever.
    val newRepr = Map() ++ equalToRepr.mapValues( q =>
      if ( q.rhs == a ) q * p else q )
    new CongruenceClosure(
      equalToRepr = newRepr,
      parents = Map() ++ ( parents - a + ( b -> ( parents( a ) ++ parents( b ) ) ) )
        .mapValues( _.map( newRepr( _ ).rhs ) ) )
      .propagate( b )
  }

  private def addTerm( a: Expr, par: Option[Expr] ): CongruenceClosure = {
    require( !equalToRepr.contains( a ) )
    new CongruenceClosure(
      equalToRepr = equalToRepr + ( a -> Refl( a ) ),
      parents = parents + ( a -> par.toSet ) )
  }

  private def addParent( a: Expr, par: Expr ): CongruenceClosure =
    new CongruenceClosure(
      equalToRepr = equalToRepr,
      parents = parents.updated( a, parents( a ) + par ) )

  private def checkCongruence( a: Expr, b: Expr ): CongruenceClosure =
    ( for {
      Apps( fa, aas ) <- equivalenceClass( a ).view
      Apps( fb, bas ) <- equivalenceClass( b ).view
      if fa == fb
      pas <- aas.zip( bas ).traverse { case ( aa, ba ) => getEqvProof( aa, ba ) }
    } yield merge( FOCongruence( fa, pas ) ) ).headOption.getOrElse( this )

  private def propagate( a0: Expr ): CongruenceClosure = {
    val a = findRepr( a0 )
    ( for ( pa <- parents( a ).view; pb <- parents( a ) ) yield ( pa, pb ) ).
      foldLeft( this )( ( c, eqn ) => c.checkCongruence( eqn._1, eqn._2 ) )
  }

  def merge( p: CongruenceProof ): CongruenceClosure =
    internalize( p.lhs ).internalize( p.rhs ).union( p )

  def merges( equations: Iterable[Formula] ): CongruenceClosure =
    equations.foldLeft( this ) { case ( c, e ) => c.merge( Input( e ) ) }

  def merges( equations: Formula* ): CongruenceClosure = merges( equations )

  def saturate( f: CongruenceClosure => CongruenceClosure ): CongruenceClosure = {
    val next = f( this )
    if ( next.representatives == representatives ) this
    else next.saturate( f )
  }
}

object CongruenceClosure {
  def apply(): CongruenceClosure =
    new CongruenceClosure(
      equalToRepr = Map(),
      parents = Map() )

  type Equation = ( Expr, Expr )
}

case class acTheory( op: Const, commutative: Boolean = true ) {
  object Op {
    def apply( a: Expr, b: Expr ): Expr = op( a, b )
    def unapply( e: Expr ): Option[( Expr, Expr )] =
      e match {
        case App( App( `op`, a ), b ) => Some( ( a, b ) )
        case _                        => None
      }
  }
  object Ops {
    def apply( as: Expr* ): Expr = apply( as )
    def apply( as: Iterable[Expr] ): Expr =
      as.reduceLeft( Op( _, _ ) )

    private def unapplyCore( e: Expr, buf: mutable.Buffer[Expr] ): Unit =
      e match {
        case Op( a, b ) =>
          unapplyCore( a, buf ); unapplyCore( b, buf )
        case _ => buf.append( e )
      }

    def unapply( e: Expr ): Some[Seq[Expr]] = {
      val buf = mutable.Buffer[Expr]()
      unapplyCore( e, buf )
      Some( buf )
    }
  }

  def normalize( es: Seq[Expr] ): Seq[Expr] =
    if ( commutative ) es.sortBy( _.hashCode ) else es

  def multisetLt( as: Seq[Expr], bs: Seq[Expr] ): Boolean = {
    val cas = Map().withDefaultValue( 0 ) ++ as.view.groupBy( identity ).mapValues( _.size )
    val cbs = Map().withDefaultValue( 0 ) ++ bs.view.groupBy( identity ).mapValues( _.size )
    as != bs && cas.forall {
      case ( x, n ) =>
        n <= cbs( x ) || cbs.exists {
          case ( y, m ) =>
            y.hashCode > x.hashCode && m > cas( y )
        }
    }
  }

  def step( cc0: CongruenceClosure ): CongruenceClosure = {
    var cc = cc0

    val E = ( for {
      a <- cc0.representatives
      e @ Op( b, c ) <- cc0.equivalenceClass( a )
    } yield {
      val lhs = Seq( a )
      val rhs = normalize( Seq( b, c ) )
      cc = cc.merge( ACTheory( op, e, Ops( rhs ) ) )
      ( lhs, rhs )
    } ).to[mutable.Queue]
    val R = mutable.Set[( Seq[Expr], Seq[Expr] )]()

    def simplify( a: Seq[Expr] ): Seq[Expr] = {
      R.find( r => r._1.diff( a ).isEmpty ) match {
        case Some( ( lhs, rhs ) ) =>
          val a_ = normalize( a.diff( lhs ) ++ rhs )
          cc = cc.merge( ACRw( op, Ops( a ), Ops( a_ ),
            cc.getEqvProof( Ops( lhs ), Ops( rhs ) ).get ) )
          simplify( a_ )
        case None => a
      }
    }

    while ( E.nonEmpty ) {
      val ( lhs, rhs ) = {
        val ( l0, r0 ) = E.dequeue()
        val ( l1, r1 ) = ( simplify( l0 ), simplify( r0 ) )
        if ( multisetLt( l1, r1 ) ) ( r1, l1 ) else ( l1, r1 )
      }
      if ( lhs != rhs ) {
        // Compose
        for {
          r @ ( lhs1, rhs1 ) <- R.toSet
          if lhs.diff( rhs1 ).isEmpty
        } {
          R -= r
          val rhs1_ = normalize( rhs1.diff( lhs ) ++ rhs )
          cc = cc.merge( ACRw( op, Ops( lhs1 ), Ops( rhs1_ ),
            cc.getEqvProof( Ops( lhs1 ), Ops( rhs1 ) ).get ) )
          R += ( lhs1 -> rhs1_ )
        }

        // Collapse
        for {
          r @ ( lhs1, rhs1 ) <- R.toSet
          if lhs.diff( lhs1 ).isEmpty
        } {
          R -= r
          val lhs1_ = normalize( lhs1.diff( lhs ) ++ rhs )
          cc = cc.merge( ACRw( op, Ops( lhs1 ), Ops( lhs1_ ),
            cc.getEqvProof( Ops( lhs1 ), Ops( rhs1 ) ).get ) )
          E += ( lhs1_ -> rhs1 )
        }

        // Superpose
        for {
          r1 @ ( lhs1, rhs1 ) <- R.toSet
          r2 @ ( lhs2, rhs2 ) <- R.toSet
          if r1.hashCode < r2.hashCode
          commonLhs = lhs1.intersect( lhs2 )
          if commonLhs.nonEmpty
        } {
          val onlyLhs1 = lhs1.diff( lhs2 )
          val onlyLhs2 = lhs2.diff( lhs1 )
          val lhs3 = normalize( rhs1 ++ onlyLhs2 )
          val middle = lhs1 ++ onlyLhs2
          val rhs3 = normalize( onlyLhs1 ++ rhs2 )
          cc = cc.merge(
            ACRw( op, Ops( middle ), Ops( lhs3 ),
              cc.getEqvProof( Ops( lhs1 ), Ops( rhs1 ) ).get ).inv *
              ACRw( op, Ops( middle ), Ops( rhs3 ),
                cc.getEqvProof( Ops( lhs2 ), Ops( rhs2 ) ).get ) )
          E += ( lhs3 -> rhs3 )
        }

        // Insert
        R += ( lhs -> rhs )
      }
    }

    // only return equivalences of terms in original set
    var res = cc0
    for {
      a <- cc0.representatives
      b <- cc0.representatives
      p <- cc.getEqvProof( a, b )
    } res = res.merge( p )
    res
  }
}

case class unitTheory( op: Const, unit: Expr ) {
  def step( cc0: CongruenceClosure ): CongruenceClosure = {
    if ( !cc0.equalToRepr.contains( unit ) ) return cc0
    var cc = cc0
    for {
      e <- cc.parents( cc.findRepr( unit ) )
      App( App( `op`, l ), r ) <- cc.equivalenceClass( e )
    } {
      for ( p <- cc.getEqvProof( e, op( l, unit ) ) )
        cc = cc.merge( p * RightUnit( op, unit, l ) )
      for ( p <- cc.getEqvProof( e, op( unit, r ) ) )
        cc = cc.merge( p * LeftUnit( op, unit, r ) )
    }
    cc
  }
}