package gapt.examples

import com.sun.org.apache.bcel.internal.generic.AllocationInstruction
import extraction.CodeGenerator
import gapt.proofs.nd._
import gapt.expr.{ TBase, _ }
import gapt.proofs.{ Ant, Checkable, Context, Sequent, Suc }
import gapt.proofs.Context.{ InductiveType, PrimRecFun }
import gapt.proofs.lk._
import org.sat4j.pb.tools.DisjunctionRHS

object example1 extends Script {

  var ctx = Context()

  implicit var systemT = ClassicalExtraction.systemT( ctx )
  println( systemT )

}

/*
object classicalExtractionTest {
  def apply( proof: NDProof )( implicit ctx: Context ): Unit = {
    val m1 = ClassicalExtraction.mrealize( proof, false )
    //val m1n = ClassicalExtraction.mrealize( proof )
    print( proof ); print( m1 ); print( " of type " ); println( m1._2.ty ); //print( "normalized: " ); print( m1n )
    println(); println()
  }
}
*/

object classicalExtractionTest {
  def apply( proof: NDProof )( implicit ctx: Context ): Unit = {
    val m1 = ClassicalExtraction.extractCases( proof )
    //val m1n = ClassicalExtraction.mrealize( proof )
    //print( proof ); print( m1 ); print( " of type " ); print( m1.ty ); println()
    println( "free vars: " + freeVariables( m1 ) )
    println(); println()
    println( CodeGenerator.apply( m1, ClassicalExtraction.systemT( ctx ) ) )
  }
}

object example2 extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val a1 = EqualityIntroRule( le"0" )
  val a2 = OrIntro1Rule( a1, hof"s(0) = 0" )
  classicalExtractionTest( a2 )

  val a3 = OrIntro2Rule( a1, hof"s(0) = 0" )
  classicalExtractionTest( a3 )
}

object example3 extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val b1 = gapt.proofs.nd.LogicalAxiom( hof"x = 0" )
  val b2 = OrIntro2Rule( b1, hof"x = 0" )
  val b6 = OrElimRule( b2, b1, b1 )
  classicalExtractionTest( b6 )
}

object example4 extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val b1 = gapt.proofs.nd.LogicalAxiom( hof"-(x = 0)" )
  val b2 = gapt.proofs.nd.LogicalAxiom( hof"x = 0" )
  val b3 = NegElimRule( b1, b2 )
  val b6 = BottomElimRule( b3, hof"x = 0" )
  classicalExtractionTest( b6 )
}

object example5 extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val b1 = gapt.proofs.nd.LogicalAxiom( hof"-(x = 0)" )
  val b2 = gapt.proofs.nd.LogicalAxiom( hof"x = 0" )
  val b3 = NegElimRule( b1, b2 )
  val b4 = NegIntroRule( b3, Ant( 1 ) )
  val b5 = NegElimRule( b4, b2 )
  val b6 = BottomElimRule( b5, hof"x = 0" )
  classicalExtractionTest( b3 )
  classicalExtractionTest( b4 )
  classicalExtractionTest( b5 )
  classicalExtractionTest( b6 )
}

object example6 extends Script {

  implicit var ctx = Context()

  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val a1 = gapt.proofs.nd.LogicalAxiom( hof"-(x = 0)" )
  val a2 = gapt.proofs.nd.LogicalAxiom( hof"x = 0" )
  val a3 = NegElimRule( a1, a2 )
  val a4 = BottomElimRule( a3, hof"x = 0" )
  val a5 = ExcludedMiddleRule( a2, Ant( 0 ), a4, Ant( 0 ) )
  classicalExtractionTest( a5 )
}

object example7 extends Script {

  implicit var ctx = Context()
  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

  val a1 = gapt.proofs.nd.LogicalAxiom( hof"-(x = 0)" )
  val a2 = gapt.proofs.nd.LogicalAxiom( hof"x = 0" )
  val a3 = NegElimRule( a1, a2 )
  val a4 = BottomElimRule( a3, hof"-(x = 0)" )
  val a5 = ExcludedMiddleRule( a4, Ant( 1 ), a1, Ant( 0 ) )
  classicalExtractionTest( a5 )
}

object example8 extends Script {

  implicit var ctx = Context()
  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += hoc"P: nat > o"

  val l = gapt.proofs.nd.ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"!x P x" ) ).
    u( ForallElimRule( _, le"n: nat" ) ).
    u( ExistsIntroRule( _, hof"?x P x" ) ).
    u( OrIntro1Rule( _, hof"?x -(P x)" ) ).
    qed
  classicalExtractionTest( l )

  val r = gapt.proofs.nd.ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"?x -(P x)" ) ).
    u( OrIntro2Rule( _, hof"?x P x" ) ).
    qed
  classicalExtractionTest( r )
}

object example9 extends Script {

  implicit var ctx = Context()
  ctx += InductiveType(
    ty"i",
    hoc"0 : i",
    hoc"s : i > i" )
  ctx += hoc"P: i > o"

  val p = gapt.proofs.nd.ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"?x P x" ) ).
    u( OrIntro1Rule( _, hof"-(?x P x)" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"-(?x P x)" ) ).
    u( OrIntro2Rule( _, hof"?x P x" ) ).
    b( ExcludedMiddleRule( _, Ant( 0 ), _, Ant( 0 ) ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"?x P x" ) ).
    u( OrIntro1Rule( _, hof"-(?x P x)" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"-(?x P x)" ) ).
    u( OrIntro2Rule( _, hof"?x P x" ) ).
    t( OrElimRule( _, _, _ ) ).
    qed
  println( p )
  classicalExtractionTest( p )
}

object example10 extends Script {
  implicit var ctx = Context()
  ctx += TBase( "i" )
  ctx += hoc"P: i > o"

  val p = gapt.proofs.nd.ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"!x P x" ) ).
    u( ForallElimRule( _, hov"v: i" ) ).
    u( ForallIntroRule( _, hof"!y P y", hov"v: i" ) ).
    qed
  classicalExtractionTest( p )
}

object example11 extends Script {
  implicit var ctx = Context()
  val s1 = gapt.proofs.lk.LogicalAxiom( hof"A" )
  val s2 = NegRightRule( s1, hof"A" )
  val s3 = NegLeftRule( s2, hof"-A" )
  val s4 = ImpRightRule( s3, hof"-(-A) -> A" )

  val nd = LKToND( s4 )
  println( nd )
  classicalExtractionTest( nd )
}

object example12 extends Script {

  implicit var ctx = Context()

  val p = gapt.proofs.nd.ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"A" ) ).
    u( OrIntro1Rule( _, hof"-A" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"-A" ) ).
    u( OrIntro2Rule( _, hof"A" ) ).
    b( ExcludedMiddleRule( _, Ant( 0 ), _, Ant( 0 ) ) ).
    qed
  classicalExtractionTest( p )
}

object example13 extends Script {
  implicit var ctx = Context()
  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )

}

/*
object extracted extends Script {
def app[A, B]( f: A => B )( arg: A ): B = f( arg )
def s( x: Int ) = x + 1
def mul( x: Int )( y: Int ) = x * y
def leq( x: Int )( y: Int ) = x <= y

def pow2( x: Int ) = x * x
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

def eq[X]( x: X )( y: X ) = x == y
def lt( x: Int )( y: Int ) = x < y
final case class Inl[A, B]( v: A ) extends Sum[A, B]
def inl[A, B]( v: A ): Sum[A, B] = new Inl( v )
def f( x: Int )( y: Int ) = x < ( y + 1 ) * ( y + 1 ) && y * y <= x

def natRec[A]( p1: A )( p2: Function2[Int, A, A] )( p3: Int ): A = {
  if ( p3 == 0 ) {
    p1
  } else {
    p2( p3 - 1, natRec( p1 )( p2 )( p3 - 1 ) )
  }
}
class NewException[A]( m: A ) extends Exception
def exception[A]( p: A ) = { new NewException( p ) }

def bar2[X, A, B]( p1: X => Boolean )( p2: A => Int )( p3: B => Int ): Int = {
  0
}

def pi1[A, B]( p: ( A, B ) ) = p._1
def bar[A, B, C]( p1: Boolean )( p2: A => C )( p3: B => C ): C = { ??? }

def pair[A, B]( p0: A )( p1: B ) = ( p0, p1 )
def efq( p: Throwable ) = { throw p }

val prog: Int => Int = {
  v_2: Int =>
    app( {
      v_0: ( Int => Int ) =>
        app( {
          v: Int => v
        } )( app( v_0 )( v_2 ) )
    } )( {
      x: Int =>
        app( app( app( natRec )( 0 ) )( {
          v_0: Int =>
            {
              v_10: Int =>
                app( app( app( bar2 )( {
                  y: Int => app( app( f )( app( s )( v_0 ) ) )( y )
                } ) )( {
                  v_11: Int => v_11
                } ) )( {
                  v_13: ( Int => Exception ) => v_10
                } )
            }
        } ) )( x )
    } )
}
}
*/
