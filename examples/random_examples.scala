import gapt.examples
import gapt.examples.Script
import gapt.examples.theories.nat.addcomm
import gapt.proofs.ProofBuilder
import gapt.proofs.lk._
import gapt.proofs.expansion._
import gapt.proofs.lk.transformations.LKToExpansionProof
import gapt.prooftool.prooftool

import scala.annotation.tailrec

object issue671 extends Script {
  import gapt.examples.theories.nat._
  val exp = LKToExpansionProof( addcomm.proof )
  val Right( lk ) = ExpansionProofToLK( exp )
  ctx.check( lk )
}

object tolk extends Script {
  import examples.theories.nat._
  val example = addcomm.proof
  val exp = LKToExpansionProof( example )
  exp.expansionSequent.foreach {
    case x =>
      println( "x" + x )
  }
  val lk: LKProof = ExpansionProofToLK( exp ).getOrElse( throw new Exception( "" ) )
  //println( lk.conclusion )
  //println( lk )
}

object result extends Script {

  /*
  def app[A, B]( f: A => B )( arg: A ): B = f( arg )
  def s( x: Int ) = x + 1
  def pi2[A, B]( p: ( A, B ) ) = p._2
  sealed trait Sum[A, B]
  final case class Inr[A, B]( v: B ) extends Sum[A, B]
  def inr[A, B]( v: B ): Sum[A, B] = new Inr( v )

  def matchSum[A, B, C]( p1: Sum[A, B] )( p2: A => C )( p3: B => C ) = {
    p1 match {
      case Inl( a ) => p2( a )
      case Inr( b ) => p3( b )
    }
  }

  def iRec[A]( p1: A )( p2: Function2[Int, A, A] )( p3: Int ): A = {
    if ( p3 == 0 ) {
      p1
    } else {
      p2( p3 - 1, iRec( p1 )( p2 )( p3 - 1 ) )
    }
  }
  def eq[X]( x: X )( y: X ) = x == y
  final case class Inl[A, B]( v: A ) extends Sum[A, B]
  def inl[A, B]( v: A ): Sum[A, B] = new Inl( v )
  class NewException[A]( m: A ) extends Exception
  def exception[A]( p: A ) = { new NewException( p ) }

  //def bar2[C](p1: Int => Boolean)(p2: (Int, Null) => C)(p3: ((Int, Null) => Exception) => C): C = {
  def bar2[P, A, C]( p1: P => Boolean )( p2: A => C )( p3: ( A => Exception ) => C ): C = {
    try {
      if ( P( n ) ) {
        true
      } else {
        p3( n )
      }
    } catch {
      case NewException( m ) && !( P( n ) ) => p2( m )
      case _                                => ???
    }
  }

  def pi1[A, B]( p: ( A, B ) ) = p._1

  def bar[A, B, C]( p1: Boolean )( p2: A => C )( p3: B => C ): C = { ??? }

  def pair[A, B]( p0: A )( p1: B ) = ( p0, p1 )
  def efq( p: Throwable ) = { throw p }

  def P( x: Int ) = true

  def id[A]( x: A ) = x

  app( app( app( bar2 )( {
    x: Int => app( P )( x )
  } ) )( {
    v: ( Int, Null ) => app( inl[( Int, Null ), ( ( Int, Null ) => Exception )] )( v )
  } ) )( {
    v_0: ( ( Int, Null ) => Exception ) => app( inr[( Int, Null ), ( ( Int, Null ) => Exception )] )( v_0 )
  } )
  ()
  */
}

object sqrtManual extends Script {
  abstract class Nat
  object Zero extends Nat
  case class Suc( n: Nat ) extends Nat

  implicit class RichNat( n1: Nat ) {
    def +( n2: Nat ): Nat = n1 match {
      case Zero           => n2
      case Suc( m1: Nat ) => Suc( m1 + n2 )
    }
    def *( n2: Nat ): Nat = n1 match {
      case Zero           => Zero
      case Suc( Zero )    => n2
      case Suc( m1: Nat ) => n2 + ( m1 * n2 )
    }
    def <=( n2: Nat ): Boolean = ( n1, n2 ) match {
      case ( Zero, _ )                        => true
      case ( Suc( _ ), Zero )                 => false
      case ( Suc( m1: Nat ), Suc( m2: Nat ) ) => m1 <= m2
    }
    def <( n2: Nat ): Boolean = ( n1, n2 ) match {
      case ( Zero, Suc( _ ) )                 => true
      case ( _, Zero )                        => false
      case ( Suc( m1: Nat ), Suc( m2: Nat ) ) => m1 < m2
    }
  }

  def toInt( n: Nat ): Int = n match {
    case Zero          => 0
    case Suc( m: Nat ) => 1 + toInt( m )
  }
  implicit def toNat( i: Int ): Nat = {
    require( i >= 0 )
    @tailrec
    def f( i: Int, a: Nat ): Nat = {
      if ( i == 0 ) a
      else f( i - 1, Suc( a ) )
    }
    f( i, Zero )
  }

  def ceilSqrt( n: Nat ): Nat = n match {
    case Zero => Zero
    case Suc( m: Nat ) =>
      val k = ceilSqrt( m )
      if ( k * k < n ) Suc( k ) else k
  }

  def floorSqrt( n: Nat ): Nat = n match {
    case Zero => Zero
    case Suc( m: Nat ) =>
      val k = floorSqrt( m )
      if ( Suc( k ) * Suc( k ) <= n ) Suc( k ) else k
  }

  def floorSqrtTailRec( n: Nat ): Nat = {
    @tailrec
    def f( n: Nat, a: Nat ): Nat = {
      if ( Suc( a ) * Suc( a ) <= n ) f( n, Suc( a ) )
      else a
    }
    f( n, Zero )
  }

  case class ValueException[A]( v: A ) extends Exception

  def floorSqrtException( n: Nat ): Nat = n match {
    case Zero => Zero
    case Suc( m: Nat ) =>
      try {
        throw ValueException( floorSqrtException( m ) )
      } catch {
        case ValueException( k: Nat ) if ( Suc( k ) * Suc( k ) <= n ) => Suc( k )
        case ValueException( k: Nat )                                 => k
      }
  }
  def g()()( f: Any ) = try f catch {
    case e => e.getMessage
  }

  println( "ceilSqrt" )
  0 to 9 map ( i => println( i + ": " + toInt( ceilSqrt( toNat( i ) ) ) ) )
  println( "floorSqrt" )
  0 to 9 map ( i => println( i + ": " + toInt( floorSqrt( toNat( i ) ) ) ) )
  println( "floorSqrtTailRec" )
  0 to 9 map ( i => println( i + ": " + toInt( floorSqrtTailRec( toNat( i ) ) ) ) )
  println( "floorSqrtException" )
  0 to 9 map ( i => println( i + ": " + toInt( floorSqrtException( toNat( i ) ) ) ) )

  println( "Testing ceilSqrt" )
  0 to 1000 foreach ( i => assert( Math.ceil( Math.sqrt( i ) ) == toInt( ceilSqrt( toNat( i ) ) ) ) )
  println( "Testing floorSqrt" )
  0 to 1000 foreach ( i => assert( Math.floor( Math.sqrt( i ) ) == toInt( floorSqrt( toNat( i ) ) ) ) )
  println( "Testing floorSqrtTailRec" )
  0 to 1000 foreach ( i => assert( Math.floor( Math.sqrt( i ) ) == toInt( floorSqrtTailRec( toNat( i ) ) ) ) )
  println( "Testing floorSqrtException" )
  0 to 1000 foreach ( i => assert( Math.floor( Math.sqrt( i ) ) == toInt( floorSqrtException( toNat( i ) ) ) ) )
}

object sqrtProofManualTry extends Script {

  import gapt.expr._
  import gapt.formats.babel.{ Notation, Precedence }
  import gapt.proofs.context.Context
  import gapt.proofs.context.update.InductiveType
  import gapt.proofs.nd._

  implicit var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += Notation.Infix( "<", Precedence.infixRel )
  ctx += Notation.Infix( "*", Precedence.timesDiv )
  ctx += Notation.Infix( "<=", Precedence.infixRel )
  ctx += hoc"'pow2': nat>nat"
  ctx += hoc"'*': nat>nat>nat"
  ctx += hoc"'<': nat>nat>o"
  ctx += hoc"'<=': nat>nat>o"
  ctx += hoc"'f': nat>nat>o"

  val peano5 = hof"!x 0 = x*0"
  val peano7 = hof"!x!y (x<y -> s(x)<s(y))"
  val lem1 = hof"!x s(pow2(s x)) < pow2(s(s x))"
  val lem2 = hof"!x pow2(x) < pow2(s x)"
  val lem4 = hof"!x!y (y<x | x<y | x=y)"
  val lem5 = hof"!x!y!z (y<z & x<y -> x<z)"
  val defleq = hof"!x!y (x<=y <-> (x=y | x<y))"
  val defpow2 = hof"!x x*x = pow2(x)"
  val defind = hof"!x!y ((f x y) <-> (x < pow2(s y) & pow2(y) <= x))"
  val thm1 =
    hof"""!y!x (
    s(x)<pow2(s y) & x<pow2(s y) & pow2(y)<=x ->
      s(x)<pow2(s y) & pow2(y)<=s(x)
  )"""
  val ind = hof"(?y (f 0 y)) & !x ((?y (f x y)) -> (?y (f (s x) y))) -> !x?y (f x y)"
  val thm = hof"!x?y (f x y)"
  val tmp = ProofBuilder.
    c( LogicalAxiom( lem5 ) ).
    u( ForallElimBlock( _, List( le"s n", le"s((s y_0) * (s y_0))", le"(s (s y_0)) * (s (s y_0))" ) ) ).
    c( LogicalAxiom( hof"!x s((s x) * (s x)) < (s (s x)) * (s (s x))" ) ).
    u( ForallElimRule( _, le"y_0:nat" ) ).
    c( LogicalAxiom( peano7 ) ).
    u( ForallElimBlock( _, List( le"n:nat", le"(s y_0) * (s y_0)" ) ) ).
    c( LogicalAxiom( hof"n < (s y_0) * (s y_0) & y_0 * y_0 <= n" ) ).
    u( AndElim1Rule( _ ) ).
    b( ImpElimRule( _, _ ) ).
    b( AndIntroRule( _, _ ) ).
    b( ImpElimRule( _, _ ) ).
    qed
  //println( tmp )

  val tmp2 = ProofBuilder.
    c( LogicalAxiom( hof"!x!y (x <= y -> x <= (s y))" ) ).
    u( ForallElimBlock( _, List( le"y_0 * y_0", le"n:nat" ) ) ).
    c( LogicalAxiom( hof"n < (s y_0) * (s y_0) & y_0 * y_0 <= n" ) ).
    u( AndElim2Rule( _ ) ).
    b( ImpElimRule( _, _ ) ).
    qed

  println( tmp2 )

  val nd = ProofBuilder.
    c( LogicalAxiom( hof"?y (n < (s y) * (s y) & y * y <= n)" ) ).
    c( tmp ).
    c( tmp2 ).
    b( AndIntroRule( _, _ ) ).
    u( ExistsIntroRule( _, hof"?y ((s n) < (s y) * (s y) & y * y <= (s n))" ) ).
    u( ContractionRule( _, hof"n < (s y_0) * (s y_0) & y_0 * y_0 <= n" ) ).
    u( ContractionRule( _, peano7 ) ).
    b( ExistsElimRule( _, _, hov"y_0:nat" ) ).
    qed
  println( nd )

}

object existsTest extends Script {
  import gapt.expr._
  import gapt.proofs.nd._
  val nd = ProofBuilder.
    c( LogicalAxiom( hof"y0 = y0" ) ).
    u( ExistsIntroRule( _, hof"?y (y = y)" ) ).
    qed
  println( nd )
}

