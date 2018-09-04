package gapt.examples

import extraction.FSharpCodeGenerator
import gapt.proofs.nd._
import gapt.expr.{ TBase, _ }
import gapt.formats.babel.{ Notation, Precedence }
import gapt.proofs
import gapt.proofs.{ Ant, Checkable, Context, ProofBuilder, Sequent, Suc }
import gapt.proofs.Context.{ InductiveType, PrimRecFun }
import gapt.proofs.lk._
import gapt.prooftool.prooftool

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
    println( FSharpCodeGenerator.apply( m1 )( ClassicalExtraction.systemT( ctx ) ) )
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

  val l = gapt.proofs.ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"!x P x" ) ).
    u( ForallElimRule( _, le"n: nat" ) ).
    u( ExistsIntroRule( _, hof"?x P x" ) ).
    u( OrIntro1Rule( _, hof"?x -(P x)" ) ).
    qed
  classicalExtractionTest( l )

  val r = gapt.proofs.ProofBuilder.
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

  val p = gapt.proofs.ProofBuilder.
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

  val p = gapt.proofs.ProofBuilder.
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

  val p = gapt.proofs.ProofBuilder.
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

object maximum extends Script {
  implicit var ctx = Context.default
  ctx += Context.InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += Notation.Infix( "<", Precedence.infixRel )
  ctx += Notation.Infix( "+", Precedence.plusMinus )
  ctx += Notation.Infix( ">=", Precedence.infixRel )
  ctx += hoc"'+': nat>nat>nat"
  ctx += hoc"'<': nat>nat>o"
  ctx += hoc"'>=': nat>nat>o"
  ctx += hoc"'f': nat>nat>o"

  val phi = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"!x2 (n >= x2 | x2 >= n)" ) ).
    u( ForallElimRule( _, hov"y : nat" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"n >= y -> s(n) >= s(y)" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"n >= y" ) ).
    b( ImpElimRule( _, _ ) ).
    u( OrIntro1Rule( _, hof"s(y) >= s(n)" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"y >= n -> s(y) >= s(n)" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"y >= n" ) ).
    b( ImpElimRule( _, _ ) ).
    u( OrIntro2Rule( _, hof"s(n) >= s(y)" ) ).
    t( OrElimRule( _, _, _ ) ).
    qed

  val phir = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"?y s(y) = x2" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"s(y) = x2" ) ).
    c( phi ).
    b( EqualityElimRule( _, _ ) ).
    b( ExistsElimRule( _, _, Ant( 0 ), hov"y: nat" ) ).
    qed
  println( s"phir.conclusion: ${phir}" )

  val phil = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"0 = x2" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"s(n) >= 0" ) ).
    u( OrIntro1Rule( _, hof"x2 >= s(n)" ) ).
    b( EqualityElimRule( _, _ ) ).
    qed
  println( s"phil.conclusion: ${phil.conclusion}" )

  val psis = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"0 = x2 | ?y s(y) = x2" ) ).
    c( phil ).
    c( phir ).
    t( OrElimRule( _, _, _ ) ).
    qed
  println( s"psis:\n$psis" )
}

object tapeExtraction extends Script {
  implicit val ctx = tapeUrban.ctx
  val nd = LKToND( eliminateDefinitions( tapeUrban.proof ) )
  if ( nd.subProofs.exists {
    case gapt.proofs.nd.InductionRule( _, _, _ ) => true
    case _                                       => false
  } )
    println( "contains Induction" )
  prooftool( nd )
  classicalExtractionTest( nd )
}

object sqrtProofManualCorrectAxiom extends Script {

  import gapt.expr._
  import gapt.formats.babel.{ Notation, Precedence }
  import gapt.proofs.Context
  import gapt.proofs.nd._

  implicit var ctx = Context.default
  ctx += Context.InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += Notation.Infix( "<", Precedence.infixRel )
  ctx += Notation.Infix( "*", Precedence.timesDiv )
  ctx += Notation.Infix( "<=", Precedence.infixRel )
  ctx += hoc"'*': nat>nat>nat"
  ctx += hoc"'<': nat>nat>o"
  ctx += hoc"'<=': nat>nat>o"

  val defleq = hof"!x!y (x<=y <-> (x=y | x<y))"
  val trans = hof"!x!y!z (x<y & y<z -> x<z)"
  val lem1 = hof"!x!y (x < y -> (s(x) = y | s(x) < y))"
  val lem3 = hof"!x!y (x = y -> s(x) = s(y))"
  val lem4 = hof"!x (s(s(x) * s(x)) < s(s(x)) * s(s(x)))"
  val lem5 = hof"!x!y (x = y -> x < s(y))"
  val symm = hof"!(x:nat)!(y:nat) (x = y -> y = x)"
  val lem7 = hof"!x!y (x < y -> x < s(y))"

  val peano1 = hof"!x (0 * x = 0)"
  val peano2 = hof"!x (s(0) * x = x)"
  val lem8 = hof"!x (x < s(x))"

  val D0 = hof"?y (0 < s(y) * s(y) & y * y <= 0)"
  val Dn = hof"?y (n < s(y) * s(y) & y * y <= n)"
  val Dsn = hof"?y (s(n) < s(y) * s(y) & y * y <= s(n))"

  val pi1Case1 = ProofBuilder.
    // Trans
    c( LogicalAxiom( trans ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(s(y0) * s(y0))", le"s(s(y0)) * s(s(y0))" ) ) ).
    c( LogicalAxiom( lem5 ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"s(n) = s(y0) * s(y0)" ) ).
    b( ImpElimRule( _, _ ) ).
    c( LogicalAxiom( lem4 ) ).
    u( ForallElimRule( _, le"y0: nat" ) ).
    b( AndIntroRule( _, _ ) ).
    b( ImpElimRule( _, _ ) ). // end Trans
    // Rewrite <->
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"s(y0) * s(y0)", le"s(n)" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( symm ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"s(n) = s(y0) * s(y0)" ) ).
    b( ImpElimRule( _, _ ) ).
    u( OrIntro1Rule( _, hof"s(y0) * s(y0) < s(n)" ) ).
    b( ImpElimRule( _, _ ) ). // end Rewrite <->
    b( AndIntroRule( _, _ ) ).
    u( ContractionRule( _, hof"s(n) = s(y0) * s(y0)" ) ).
    u( ExistsIntroRule( _, Dsn ) ).
    qed
  //println( pi3 )

  val pi1Case2 = ProofBuilder.
    c( LogicalAxiom( hof"s(n) < s(y0) * s(y0)" ) ).
    // Rewrite <->
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"s(n)" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( lem7 ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"n: nat" ) ) ).
    c( LogicalAxiom( hof"y0 * y0 < n" ) ).
    b( ImpElimRule( _, _ ) ).
    u( OrIntro2Rule( _, hof"y0 * y0 = s(n)" ) ).
    b( ImpElimRule( _, _ ) ). // end Rewrite <->
    b( AndIntroRule( _, _ ) ).
    u( ExistsIntroRule( _, Dsn ) ).
    qed
  //println( pi4 )

  val pi1 = ProofBuilder.
    c( LogicalAxiom( lem1 ) ).
    u( ForallElimBlock( _, List( le"n:nat", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"n < s(y0) * s(y0) & y0 * y0 <= n" ) ).
    u( AndElim1Rule( _ ) ).
    b( ImpElimRule( _, _ ) ).
    c( pi1Case1 ).
    c( pi1Case2 ).
    t( OrElimRule( _, _, _ ) ).
    qed
  //println( pi1 )

  val pi2Case1 = ProofBuilder.
    // Trans
    c( LogicalAxiom( trans ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(s(y0) * s(y0))", le"s(s(y0)) * s(s(y0))" ) ) ).
    c( LogicalAxiom( lem5 ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"s(n) = s(y0) * s(y0)" ) ).
    b( ImpElimRule( _, _ ) ).
    c( LogicalAxiom( lem4 ) ).
    u( ForallElimRule( _, le"y0: nat" ) ).
    b( AndIntroRule( _, _ ) ).
    b( ImpElimRule( _, _ ) ). // end Trans
    // Rewrite <->
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"s(y0) * s(y0)", le"s(n)" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( symm ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"s(n) = s(y0) * s(y0)" ) ).
    b( ImpElimRule( _, _ ) ).
    u( OrIntro1Rule( _, hof"s(y0) * s(y0) < s(n)" ) ).
    b( ImpElimRule( _, _ ) ). // end Rewrite <->
    b( AndIntroRule( _, _ ) ).
    u( ContractionRule( _, hof"s(n) = s(y0) * s(y0)" ) ).
    u( ExistsIntroRule( _, Dsn ) ).
    qed
  //println( pi32 )

  val pi2Case2 = ProofBuilder.
    c( LogicalAxiom( hof"s(n) < s(y0) * s(y0)" ) ).
    // Rewrite <->
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"s(n)" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( lem5 ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"n:nat" ) ) ).
    c( LogicalAxiom( hof"y0 * y0 = n" ) ).
    b( ImpElimRule( _, _ ) ).
    u( OrIntro2Rule( _, hof"y0 * y0 = s(n)" ) ).
    b( ImpElimRule( _, _ ) ). // end Rewrite <->
    b( AndIntroRule( _, _ ) ).
    u( ExistsIntroRule( _, Dsn ) ).
    qed
  //println( case2 )

  val pi2 = ProofBuilder.
    c( LogicalAxiom( lem1 ) ).
    u( ForallElimBlock( _, List( le"n:nat", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"n < s(y0) * s(y0) & y0 * y0 <= n" ) ).
    u( AndElim1Rule( _ ) ).
    b( ImpElimRule( _, _ ) ).
    c( pi2Case1 ).
    c( pi2Case2 ).
    t( OrElimRule( _, _, _ ) ).
    qed
  //println( pi22 )

  val pi0 = ProofBuilder.
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"n:nat" ) ) ).
    u( AndElim1Rule( _ ) ).
    c( LogicalAxiom( hof"n < s(y0) * s(y0) & y0 * y0 <= n" ) ).
    u( AndElim2Rule( _ ) ).
    b( ImpElimRule( _, _ ) ).
    c( pi2 ).
    c( pi1 ).
    t( OrElimRule( _, _, _ ) ).
    u( ContractionRule( _, hof"n < s(y0) * s(y0) & y0 * y0 <= n" ) ).
    u( ContractionRule( _, hof"n < s(y0) * s(y0) & y0 * y0 <= n" ) ).
    u( ContractionRule( _, lem4 ) ).
    u( ContractionRule( _, lem5 ) ).
    u( ContractionRule( _, defleq ) ).
    u( ContractionRule( _, defleq ) ).
    u( ContractionRule( _, defleq ) ).
    u( ContractionRule( _, defleq ) ).
    u( ContractionRule( _, trans ) ).
    u( ContractionRule( _, symm ) ).
    u( ContractionRule( _, lem1 ) ).
    qed
  //println( pi0 )

  val step = ProofBuilder.
    c( LogicalAxiom( Dn ) ).
    c( pi0 ).
    b( ExistsElimRule( _, _, hov"y0:nat" ) ).
    qed
  //println( step )

  val icStep = InductionCase( step, hoc"s", List( step.endSequent.indexOfInAnt( Dn ) ), List( hov"n:nat" ) )

  val base = ProofBuilder.
    c( LogicalAxiom( peano2 ) ).
    u( ForallElimRule( _, le"s(0)" ) ).
    c( LogicalAxiom( lem8 ) ).
    u( ForallElimRule( _, le"0:nat" ) ).
    b( EqualityElimRule( _, _, hof"0 < x", hov"x:nat" ) ).
    // begin 0 * 0 <= 0
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"0 * 0", le"0:nat" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( peano1 ) ).
    u( ForallElimRule( _, le"0:nat" ) ).
    u( OrIntro1Rule( _, hof"0 * 0 < 0" ) ).
    b( ImpElimRule( _, _ ) ). // end 0 * 0 <= 0
    b( AndIntroRule( _, _ ) ).
    u( ExistsIntroRule( _, D0 ) ).
    qed
  //println( base )
  val icBase = InductionCase( base, hoc"0:nat", List.empty, List.empty )

  val proof = ProofBuilder.
    c( InductionRule( List( icBase, icStep ), Abs( hov"n:nat", Dn ), le"n:nat" ) ).
    u( ForallIntroRule( _, hov"n:nat", hov"n:nat" ) ).
    u( ContractionRule( _, defleq ) ).
    qed
  //println( proof )
  prooftool( proof )
  import extraction.{ ScalaCodeGenerator, FSharpCodeGenerator }
  val m1 = ClassicalExtraction.extractCases( proof )
  ScalaCodeGenerator( m1 )( ClassicalExtraction.systemT( ctx ) )

  val m = MRealizability.mrealize( proof )
  implicit var systemT = MRealizability.systemT( ctx )
  println( "free vars: " + freeVariables( m._2( le"s(s(s(s(0))))" ) ) )
  println( normalize( m._2( le"s(s(s(s(0))))" ) ) )
}

object extractedCorrectAxiom extends Script {
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

  def natRec[A]( p1: A )( p2: ( Int => A => A ) )( p3: Int ): A = {
    if ( p3 == 0 ) {
      p1
    } else {
      p2( p3 - 1 )( natRec( p1 )( p2 )( p3 - 1 ) )
    }
  }

  class NewException[A]( m: A ) extends Exception
  def exception[A]( p: A ) = { new NewException( p ) }

  def bar2[X, A, B, C]( p1: X => Boolean )( p2: A => C )( p3: B => C ): C = { ??? }

  def pi1[A, B]( p: ( A, B ) ) = p._1
  def bar[A, B, C]( p2: A => C )( p3: B => C ): C = { ??? }

  def pair[A, B]( p0: A )( p1: B ): Tuple2[A, B] = ( p0, p1 )
  def efq( p: Throwable ) = {
    println( "in efq" )
    throw p
  }

  val prog = ( {
    v_13: ( Int => ( Int => ( Unit => Unit ) ) ) =>
      ( {
        v_7: ( Int => ( Int => ( Unit => Unit ) ) ) =>
          ( {
            v_9: ( Int => Unit ) =>
              ( {
                v_7: ( Int => ( Int => ( Unit => Unit ) ) ) =>
                  ( {
                    v_6: ( Int => ( Int => ( Int => ( Tuple2[Unit, Unit] => Unit ) ) ) ) =>
                      ( {
                        v_10: ( Int => ( Int => ( Unit => Unit ) ) ) =>
                          ( {
                            v_5: ( Int => ( Int => ( Unit => Sum[Unit, Unit] ) ) ) =>
                              ( {
                                v_2: ( Int => Unit ) =>
                                  ( {
                                    v_0: ( Int => Unit ) =>
                                      ( {
                                        v: ( Int => Unit ) =>
                                          ( {
                                            v_1: ( Int => ( Int => Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] ) ) =>
                                              ( {
                                                n: Int =>
                                                  natRec[Tuple2[Int, Tuple2[Unit, Unit]]]( pair[Int, Tuple2[Unit, Unit]]( 0 )( pair[Unit, Unit]( () )( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_1( mul( 0 )( 0 ) )( 0 ) )( inl[Unit, Unit]( v_2( 0 ) ) ) ) ) )( ( {
                                                    n: Int =>
                                                      ( {
                                                        v_3: Tuple2[Int, Tuple2[Unit, Unit]] =>
                                                          matchSum( pi1[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_1( mul( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) )( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) )( n ) )( pi2[Unit, Unit]( pi2[Int, Tuple2[Unit, Unit]]( v_3 ) ) ) )( ( {
                                                            v_12: Unit =>
                                                              matchSum( v_5( n )( mul( s( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) )( s( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) ) )( pi1[Unit, Unit]( pi2[Int, Tuple2[Unit, Unit]]( v_3 ) ) ) )( ( {
                                                                v_8: Unit => pair[Int, Tuple2[Unit, Unit]]( s( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) )( pair[Unit, Unit]( v_6( s( n ) )( s( mul( s( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) )( s( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) ) ) )( mul( s( s( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) ) )( s( s( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) ) ) )( pair[Unit, Unit]( v_7( s( n ) )( mul( s( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) )( s( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) ) )( v_8 ) )( v_9( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) ) ) )( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_1( mul( s( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) )( s( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) ) )( s( n ) ) )( inl[Unit, Unit]( v_10( s( n ) )( mul( s( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) )( s( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) ) )( v_8 ) ) ) ) )
                                                              } ) )( ( {
                                                                v_11: Unit => pair[Int, Tuple2[Unit, Unit]]( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) )( pair[Unit, Unit]( v_11 )( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_1( mul( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) )( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) )( s( n ) ) )( inr[Unit, Unit]( v_7( mul( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) )( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) )( n )( v_12 ) ) ) ) )
                                                              } ) )
                                                          } ) )( ( {
                                                            v_14: Unit =>
                                                              matchSum( v_5( n )( mul( s( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) )( s( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) ) )( pi1[Unit, Unit]( pi2[Int, Tuple2[Unit, Unit]]( v_3 ) ) ) )( ( {
                                                                v_8: Unit => pair[Int, Tuple2[Unit, Unit]]( s( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) )( pair[Unit, Unit]( v_6( s( n ) )( s( mul( s( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) )( s( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) ) ) )( mul( s( s( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) ) )( s( s( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) ) ) )( pair[Unit, Unit]( v_7( s( n ) )( mul( s( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) )( s( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) ) )( v_8 ) )( v_9( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) ) ) )( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_1( mul( s( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) )( s( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) ) )( s( n ) ) )( inl[Unit, Unit]( v_10( s( n ) )( mul( s( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) )( s( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) ) )( v_8 ) ) ) ) )
                                                              } ) )( ( {
                                                                v_11: Unit => pair[Int, Tuple2[Unit, Unit]]( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) )( pair[Unit, Unit]( v_11 )( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_1( mul( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) )( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) )( s( n ) ) )( inr[Unit, Unit]( v_13( mul( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) )( pi1[Int, Tuple2[Unit, Unit]]( v_3 ) ) )( n )( v_14 ) ) ) ) )
                                                              } ) )
                                                          } ) )
                                                      } )
                                                  } ) )( n )
                                              } )
                                          } )
                                      } )
                                  } )
                              } )
                          } )
                      } )
                  } )
              } )
          } )
      } )
  } )

  val arg1 = { _: Int => { ( _: Int ) => ( { _: Unit => () } ) } }
  val arg2 = { _: Int => { ( _: Int ) => ( { _: Unit => () } ) } }
  val arg3 = { _: Int =>
    { ( _: Int ) =>
      ( { _: Int =>
        ( { _: Tuple2[Unit, Unit] =>
          ()
        } )
      } )
    }
  }
  // val lem1 = hof"!x!y (x < y -> (s(x) = y | s(x) < y))"
  val arg4 = { x: Int =>
    { ( y: Int ) =>
      ( { _: Unit =>
        {
          //println( s"v_9: $x, $y" )
          if ( s( x ) == y ) {
            //println( "case s(x) == y\n" )
            inl[Unit, Unit]( () )
          } else if ( s( x ) < y ) {
            //println( "case s(x) < y\n" )
            inr[Unit, Unit]( () )
          } else {
            //println( "case s(x) > y\n" )
            // Don't care
            //inl[Unit, Unit]( () )
            inr[Unit, Unit]( () )
          }
        };
      } )
    }
  }
  val arg5 = { _: Int => { ( _: Int ) => ( { _: Unit => () } ) } }
  val arg6 = { _: Int => () }
  val arg7 = { _: Int => { ( _: Int ) => ( { _: Unit => () } ) } }
  val arg9 = { _: Int => () }

  //val defleq = hof"!x!y ((x<=y -> (x=y | x<y))) & ((x=y | x < y) -> x<=y))"

  val arg10 = { x: Int =>
    { ( y: Int ) =>
      ( { _: Unit =>
        //println( s"v_1: $x, $y" )
        /*
    inr[Unit, Unit]( () )
    */
        // Don't understand this yet
        if ( x == y ) {
          //println( "case x == y\n" )
          inl[Unit, Unit]( () )
        } else if ( x < y ) {
          //println( "case x < y\n" )
          inr[Unit, Unit]( () )
        } else {
          //println( "case x > y\n" )
          // Don't care
          inr[Unit, Unit]( () )
        }
      }, { _: Sum[Unit, Unit] => () } )
    }
  }
  val arg11 = { _: Int => () }
  val arg12 = { _: Int => () }

  val realProg = prog( arg1 )( arg2 )( arg11 )( arg5 )( arg3 )( arg5 )( arg4 )( arg11 )( arg11 )( arg12 )( arg10 )

  0 to 4 map ( i => println( s"$i: ${realProg( i )._1}" ) )
  println( "Testing 1000 inputs" )
  0 to 1000 foreach ( i => {
    if ( Math.floor( Math.sqrt( i ) ).toInt != realProg( i )._1 ) {
      throw new Exception( s"realProg failed at input $i." )
    }
  } )
}

object sqrtProofManualCorrectAxiomClassical extends Script {

  import gapt.expr._
  import gapt.formats.babel.{ Notation, Precedence }
  import gapt.proofs.Context
  import gapt.proofs.nd._

  implicit var ctx = Context.default
  ctx += Context.InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += Notation.Infix( "<", Precedence.infixRel )
  ctx += Notation.Infix( "*", Precedence.timesDiv )
  ctx += Notation.Infix( "<=", Precedence.infixRel )
  ctx += hoc"'*': nat>nat>nat"
  ctx += hoc"'<': nat>nat>o"
  ctx += hoc"'<=': nat>nat>o"

  val defleq = hof"!x!y (x<=y <-> (x=y | x<y))"
  val trans = hof"!x!y!z (x<y & y<z -> x<z)"
  val lem1 = hof"!x!y (x < y -> (s(x) = y | s(x) < y))"
  val lem3 = hof"!x!y (x = y -> s(x) = s(y))"
  val lem4 = hof"!x (s(s(x) * s(x)) < s(s(x)) * s(s(x)))"
  val lem5 = hof"!x!y (x = y -> x < s(y))"
  val symm = hof"!(x:nat)!(y:nat) (x = y -> y = x)"
  val lem7 = hof"!x!y (x < y -> x < s(y))"

  val peano1 = hof"!x (0 * x = 0)"
  val peano2 = hof"!x (s(0) * x = x)"
  val lem8 = hof"!x (x < s(x))"

  val D0 = hof"?y (0 < s(y) * s(y) & y * y <= 0)"
  val Dn = hof"?y (n < s(y) * s(y) & y * y <= n)"
  val Dsn = hof"?y (s(n) < s(y) * s(y) & y * y <= s(n))"

  val pi1Case1 = ProofBuilder.
    // Trans
    c( LogicalAxiom( trans ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(s(y0) * s(y0))", le"s(s(y0)) * s(s(y0))" ) ) ).
    c( LogicalAxiom( lem5 ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"s(n) = s(y0) * s(y0)" ) ).
    b( ImpElimRule( _, _ ) ).
    c( LogicalAxiom( lem4 ) ).
    u( ForallElimRule( _, le"y0: nat" ) ).
    b( AndIntroRule( _, _ ) ).
    b( ImpElimRule( _, _ ) ). // end Trans
    // Rewrite <->
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"s(y0) * s(y0)", le"s(n)" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( symm ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"s(n) = s(y0) * s(y0)" ) ).
    b( ImpElimRule( _, _ ) ).
    u( OrIntro1Rule( _, hof"s(y0) * s(y0) < s(n)" ) ).
    b( ImpElimRule( _, _ ) ). // end Rewrite <->
    b( AndIntroRule( _, _ ) ).
    u( ContractionRule( _, hof"s(n) = s(y0) * s(y0)" ) ).
    u( ExistsIntroRule( _, Dsn ) ).
    qed
  //println( pi3 )

  val pi1Case2 = ProofBuilder.
    c( LogicalAxiom( hof"s(n) < s(y0) * s(y0)" ) ).
    // Rewrite <->
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"s(n)" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( lem7 ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"n: nat" ) ) ).
    c( LogicalAxiom( hof"y0 * y0 < n" ) ).
    b( ImpElimRule( _, _ ) ).
    u( OrIntro2Rule( _, hof"y0 * y0 = s(n)" ) ).
    b( ImpElimRule( _, _ ) ). // end Rewrite <->
    b( AndIntroRule( _, _ ) ).
    u( ExistsIntroRule( _, Dsn ) ).
    qed
  //println( pi4 )

  val pi1 = ProofBuilder.
    c( LogicalAxiom( lem1 ) ).
    u( ForallElimBlock( _, List( le"n:nat", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"n < s(y0) * s(y0) & y0 * y0 <= n" ) ).
    u( AndElim1Rule( _ ) ).
    b( ImpElimRule( _, _ ) ).
    c( pi1Case1 ).
    c( pi1Case2 ).
    t( OrElimRule( _, _, _ ) ).
    qed
  //println( pi1 )

  val pi2Case1 = ProofBuilder.
    // Trans
    c( LogicalAxiom( trans ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(s(y0) * s(y0))", le"s(s(y0)) * s(s(y0))" ) ) ).
    c( LogicalAxiom( lem5 ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"s(n) = s(y0) * s(y0)" ) ).
    b( ImpElimRule( _, _ ) ).
    c( LogicalAxiom( lem4 ) ).
    u( ForallElimRule( _, le"y0: nat" ) ).
    b( AndIntroRule( _, _ ) ).
    b( ImpElimRule( _, _ ) ). // end Trans
    // Rewrite <->
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"s(y0) * s(y0)", le"s(n)" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( symm ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"s(n) = s(y0) * s(y0)" ) ).
    b( ImpElimRule( _, _ ) ).
    u( OrIntro1Rule( _, hof"s(y0) * s(y0) < s(n)" ) ).
    b( ImpElimRule( _, _ ) ). // end Rewrite <->
    b( AndIntroRule( _, _ ) ).
    u( ContractionRule( _, hof"s(n) = s(y0) * s(y0)" ) ).
    u( ExistsIntroRule( _, Dsn ) ).
    qed
  //println( pi32 )

  val pi2Case2 = ProofBuilder.
    c( LogicalAxiom( hof"s(n) < s(y0) * s(y0)" ) ).
    // Rewrite <->
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"s(n)" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( lem5 ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"n:nat" ) ) ).
    c( LogicalAxiom( hof"y0 * y0 = n" ) ).
    b( ImpElimRule( _, _ ) ).
    u( OrIntro2Rule( _, hof"y0 * y0 = s(n)" ) ).
    b( ImpElimRule( _, _ ) ). // end Rewrite <->
    b( AndIntroRule( _, _ ) ).
    u( ExistsIntroRule( _, Dsn ) ).
    qed
  //println( case2 )

  val pi2 = ProofBuilder.
    c( LogicalAxiom( lem1 ) ).
    u( ForallElimBlock( _, List( le"n:nat", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"n < s(y0) * s(y0) & y0 * y0 <= n" ) ).
    u( AndElim1Rule( _ ) ).
    b( ImpElimRule( _, _ ) ).
    c( pi2Case1 ).
    c( pi2Case2 ).
    t( OrElimRule( _, _, _ ) ).
    qed
  //println( pi22 )

  val pi0 = ProofBuilder.
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"n:nat" ) ) ).
    u( AndElim1Rule( _ ) ).
    c( LogicalAxiom( hof"n < s(y0) * s(y0) & y0 * y0 <= n" ) ).
    u( AndElim2Rule( _ ) ).
    b( ImpElimRule( _, _ ) ).
    c( pi2 ).
    c( pi1 ).
    t( OrElimRule( _, _, _ ) ).
    u( ContractionRule( _, hof"n < s(y0) * s(y0) & y0 * y0 <= n" ) ).
    u( ContractionRule( _, hof"n < s(y0) * s(y0) & y0 * y0 <= n" ) ).
    u( ContractionRule( _, lem4 ) ).
    u( ContractionRule( _, lem5 ) ).
    u( ContractionRule( _, defleq ) ).
    u( ContractionRule( _, defleq ) ).
    u( ContractionRule( _, defleq ) ).
    u( ContractionRule( _, defleq ) ).
    u( ContractionRule( _, trans ) ).
    u( ContractionRule( _, symm ) ).
    u( ContractionRule( _, lem1 ) ).
    qed
  //println( pi0 )

  val step = ProofBuilder.
    c( LogicalAxiom( Dn ) ).
    c( pi0 ).
    b( ExistsElimRule( _, _, hov"y0:nat" ) ).
    qed
  //println( step )

  val classicalStep = ProofBuilder.
    c( step ).
    c( LogicalAxiom( -Dn ) ).
    c( LogicalAxiom( Dn ) ).
    b( NegElimRule( _, _ ) ).
    u( BottomElimRule( _, Dsn ) ).
    b( ExcludedMiddleRule( _, _ ) ).
    qed

  val icStep = InductionCase( classicalStep, hoc"s", List( classicalStep.endSequent.indexOfInAnt( Dn ) ), List( hov"n:nat" ) )

  val base = ProofBuilder.
    c( LogicalAxiom( peano2 ) ).
    u( ForallElimRule( _, le"s(0)" ) ).
    c( LogicalAxiom( lem8 ) ).
    u( ForallElimRule( _, le"0:nat" ) ).
    b( EqualityElimRule( _, _, hof"0 < x", hov"x:nat" ) ).
    // begin 0 * 0 <= 0
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"0 * 0", le"0:nat" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( peano1 ) ).
    u( ForallElimRule( _, le"0:nat" ) ).
    u( OrIntro1Rule( _, hof"0 * 0 < 0" ) ).
    b( ImpElimRule( _, _ ) ). // end 0 * 0 <= 0
    b( AndIntroRule( _, _ ) ).
    u( ExistsIntroRule( _, D0 ) ).
    qed
  //println( base )
  val icBase = InductionCase( base, hoc"0:nat", List.empty, List.empty )

  val proof = ProofBuilder.
    c( InductionRule( List( icBase, icStep ), Abs( hov"n:nat", Dn ), le"n:nat" ) ).
    u( ForallIntroRule( _, hov"n:nat", hov"n:nat" ) ).
    u( ContractionRule( _, defleq ) ).
    qed
  //println( proof )
  prooftool( proof )
  import extraction.{ ScalaCodeGenerator, FSharpCodeGenerator }
  val m1 = ClassicalExtraction.extractCases( proof )
  ScalaCodeGenerator( m1 )( ClassicalExtraction.systemT( ctx ) )

  val m = MRealizability.mrealize( proof )
  implicit var systemT = MRealizability.systemT( ctx )
  println( "free vars: " + freeVariables( m._2( le"s(s(s(s(0))))" ) ) )
  println( normalize( m._2( le"s(s(s(s(0))))" ) ) )
}

object extractedCorrectAxiomClassicalEMnoAbs extends Script {
  def s( x: Int ) = x + 1
  def mul( x: Int )( y: Int ) = x * y
  def leq( x: Int )( y: Int ) = x <= y

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

  def natRec[A]( p1: A )( p2: ( Int => A => A ) )( p3: Int ): A = {
    if ( p3 == 0 ) {
      p1
    } else {
      p2( p3 - 1 )( natRec( p1 )( p2 )( p3 - 1 ) )
    }
  }

  class NewException[A]( m: A ) extends Exception { def getVal: A = m }
  def exception[A]( p: A ) = { new NewException( p ) }

  def pi1[A, B]( p: ( A, B ) ) = p._1
  def bar[A, B, C]( p2: A => C )( p3: B => C ): C = { ??? }

  def pair[A, B]( p0: A )( p1: B ): Tuple2[A, B] = ( p0, p1 )
  def efq( p: Throwable ) = { throw p }

  val prog = ( {
    v_13: ( Int => ( Int => ( Unit => Unit ) ) ) =>
      ( {
        v_7: ( Int => ( Int => ( Unit => Unit ) ) ) =>
          ( {
            v_9: ( Int => Unit ) =>
              ( {
                v_7: ( Int => ( Int => ( Unit => Unit ) ) ) =>
                  ( {
                    v_6: ( Int => ( Int => ( Int => ( Tuple2[Unit, Unit] => Unit ) ) ) ) =>
                      ( {
                        v_10: ( Int => ( Int => ( Unit => Unit ) ) ) =>
                          ( {
                            v_5: ( Int => ( Int => ( Unit => Sum[Unit, Unit] ) ) ) =>
                              ( {
                                v_2: ( Int => Unit ) =>
                                  ( {
                                    v_0: ( Int => Unit ) =>
                                      ( {
                                        v: ( Int => Unit ) =>
                                          ( {
                                            v_1: ( Int => ( Int => Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] ) ) =>
                                              ( {
                                                n: Int =>
                                                  natRec( pair( 0 )( pair( () )( pi2( v_1( mul( 0 )( 0 ) )( 0 ) )( inl[Unit, Unit]( v_2( 0 ) ) ) ) ) )( ( {
                                                    n: Int =>
                                                      ( {
                                                        v_3: Tuple2[Int, Tuple2[Unit, Unit]] =>
                                                          try {
                                                            ( {
                                                              v_15: ( Tuple2[Int, Tuple2[Unit, Unit]] => Exception ) => efq( v_15( v_3 ) )
                                                            } )( exception )
                                                          } catch {
                                                            case e: NewException[Tuple2[Int, Tuple2[Unit, Unit]]] => ( {
                                                              v_3: Tuple2[Int, Tuple2[Unit, Unit]] =>
                                                                matchSum( pi1( v_1( mul( pi1( v_3 ) )( pi1( v_3 ) ) )( n ) )( pi2( pi2( v_3 ) ) ) )( ( {
                                                                  v_12: Unit =>
                                                                    matchSum( v_5( n )( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( pi1( pi2( v_3 ) ) ) )( ( {
                                                                      v_8: Unit => pair( s( pi1( v_3 ) ) )( pair( v_6( s( n ) )( s( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) ) )( mul( s( s( pi1( v_3 ) ) ) )( s( s( pi1( v_3 ) ) ) ) )( pair( v_7( s( n ) )( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( v_8 ) )( v_9( pi1( v_3 ) ) ) ) )( pi2( v_1( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( s( n ) ) )( inl[Unit, Unit]( v_10( s( n ) )( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( v_8 ) ) ) ) )
                                                                    } ) )( ( {
                                                                      v_11: Unit => pair( pi1( v_3 ) )( pair( v_11 )( pi2( v_1( mul( pi1( v_3 ) )( pi1( v_3 ) ) )( s( n ) ) )( inr[Unit, Unit]( v_7( mul( pi1( v_3 ) )( pi1( v_3 ) ) )( n )( v_12 ) ) ) ) )
                                                                    } ) )
                                                                } ) )( ( {
                                                                  v_14: Unit =>
                                                                    matchSum( v_5( n )( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( pi1( pi2( v_3 ) ) ) )( ( {
                                                                      v_8: Unit => pair( s( pi1( v_3 ) ) )( pair( v_6( s( n ) )( s( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) ) )( mul( s( s( pi1( v_3 ) ) ) )( s( s( pi1( v_3 ) ) ) ) )( pair( v_7( s( n ) )( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( v_8 ) )( v_9( pi1( v_3 ) ) ) ) )( pi2( v_1( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( s( n ) ) )( inl[Unit, Unit]( v_10( s( n ) )( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( v_8 ) ) ) ) )
                                                                    } ) )( ( {
                                                                      v_11: Unit => pair( pi1( v_3 ) )( pair( v_11 )( pi2( v_1( mul( pi1( v_3 ) )( pi1( v_3 ) ) )( s( n ) ) )( inr[Unit, Unit]( v_13( mul( pi1( v_3 ) )( pi1( v_3 ) ) )( n )( v_14 ) ) ) ) )
                                                                    } ) )
                                                                } ) )
                                                            } )( e.getVal )
                                                            case e => println( "BUG" ); throw e
                                                          }
                                                      } )
                                                  } ) )( n )
                                              } )
                                          } )
                                      } )
                                  } )
                              } )
                          } )
                      } )
                  } )
              } )
          } )
      } )
  } )

  val arg1 = { _: Int => { ( _: Int ) => ( { _: Unit => () } ) } }
  val arg2 = { _: Int => { ( _: Int ) => ( { _: Unit => () } ) } }
  val arg3 = { _: Int =>
    { ( _: Int ) =>
      ( { _: Int =>
        ( { _: Tuple2[Unit, Unit] =>
          ()
        } )
      } )
    }
  }
  // val lem1 = hof"!x!y (x < y -> (s(x) = y | s(x) < y))"
  val arg4 = { x: Int =>
    { ( y: Int ) =>
      ( { _: Unit =>
        {
          //println( s"v_9: $x, $y" )
          if ( s( x ) == y ) {
            //println( "case s(x) == y\n" )
            inl[Unit, Unit]( () )
          } else if ( s( x ) < y ) {
            //println( "case s(x) < y\n" )
            inr[Unit, Unit]( () )
          } else {
            //println( "case s(x) > y\n" )
            // Don't care
            //inl[Unit, Unit]( () )
            inr[Unit, Unit]( () )
          }
        };
      } )
    }
  }
  val arg5 = { _: Int => { ( _: Int ) => ( { _: Unit => () } ) } }
  val arg6 = { _: Int => () }
  val arg7 = { _: Int => { ( _: Int ) => ( { _: Unit => () } ) } }
  val arg9 = { _: Int => () }

  //val defleq = hof"!x!y ((x<=y -> (x=y | x<y))) & ((x=y | x < y) -> x<=y))"

  val arg10 = { x: Int =>
    { ( y: Int ) =>
      ( { _: Unit =>
        //println( s"v_1: $x, $y" )
        /*
inr[Unit, Unit]( () )
*/
        // Don't understand this yet
        if ( x == y ) {
          //println( "case x == y\n" )
          inl[Unit, Unit]( () )
        } else if ( x < y ) {
          //println( "case x < y\n" )
          inr[Unit, Unit]( () )
        } else {
          //println( "case x > y\n" )
          // Don't care
          inr[Unit, Unit]( () )
        }
      }, { _: Sum[Unit, Unit] => () } )
    }
  }
  val arg11 = { _: Int => () }
  val arg12 = { _: Int => () }

  val realProg = prog( arg1 )( arg2 )( arg11 )( arg5 )( arg3 )( arg5 )( arg4 )( arg11 )( arg11 )( arg12 )( arg10 )

  0 to 4 map ( i => println( s"$i: ${realProg( i )._1}" ) )
  println( "Testing 1000 inputs" )
  0 to 1000 foreach ( i => {
    if ( Math.floor( Math.sqrt( i ) ).toInt != realProg( i )._1 ) {
      throw new Exception( s"realProg failed at input $i." )
    }
  } )
}

object sqrtProofManualCorrectAxiomClassicalDifferentEMFormulas extends Script {

  import gapt.expr._
  import gapt.formats.babel.{ Notation, Precedence }
  import gapt.proofs.Context
  import gapt.proofs.nd._

  implicit var ctx = Context.default
  ctx += Context.InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += Notation.Infix( "<", Precedence.infixRel )
  ctx += Notation.Infix( "*", Precedence.timesDiv )
  ctx += Notation.Infix( "<=", Precedence.infixRel )
  ctx += hoc"'*': nat>nat>nat"
  ctx += hoc"'<': nat>nat>o"
  ctx += hoc"'<=': nat>nat>o"

  val defleq = hof"!x!y (x<=y <-> (x=y | x<y))"
  val trans = hof"!x!y!z (x<y & y<z -> x<z)"
  val lem1 = hof"!x!y (x < y -> (s(x) = y | s(x) < y))"
  val lem3 = hof"!x!y (x = y -> s(x) = s(y))"
  val lem4 = hof"!x (s(s(x) * s(x)) < s(s(x)) * s(s(x)))"
  val lem5 = hof"!x!y (x = y -> x < s(y))"
  val symm = hof"!(x:nat)!(y:nat) (x = y -> y = x)"
  val lem7 = hof"!x!y (x < y -> x < s(y))"

  val peano1 = hof"!x (0 * x = 0)"
  val peano2 = hof"!x (s(0) * x = x)"
  val lem8 = hof"!x (x < s(x))"

  val D0 = hof"?y (0 < s(y) * s(y) & y * y <= 0)"
  val Dn = hof"?y (n < s(y) * s(y) & y * y <= n)"
  val Dsn = hof"?y (s(n) < s(y) * s(y) & y * y <= s(n))"

  val pi1Case1 = ProofBuilder.
    // Trans
    c( LogicalAxiom( trans ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(s(y0) * s(y0))", le"s(s(y0)) * s(s(y0))" ) ) ).
    c( LogicalAxiom( lem5 ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"s(n) = s(y0) * s(y0)" ) ).
    b( ImpElimRule( _, _ ) ).
    c( LogicalAxiom( lem4 ) ).
    u( ForallElimRule( _, le"y0: nat" ) ).
    b( AndIntroRule( _, _ ) ).
    b( ImpElimRule( _, _ ) ). // end Trans
    // Rewrite <->
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"s(y0) * s(y0)", le"s(n)" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( symm ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"s(n) = s(y0) * s(y0)" ) ).
    b( ImpElimRule( _, _ ) ).
    u( OrIntro1Rule( _, hof"s(y0) * s(y0) < s(n)" ) ).
    b( ImpElimRule( _, _ ) ). // end Rewrite <->
    b( AndIntroRule( _, _ ) ).
    u( ContractionRule( _, hof"s(n) = s(y0) * s(y0)" ) ).
    u( ExistsIntroRule( _, Dsn ) ).
    qed
  //println( pi3 )

  val pi1Case2 = ProofBuilder.
    c( LogicalAxiom( hof"s(n) < s(y0) * s(y0)" ) ).
    // Rewrite <->
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"s(n)" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( lem7 ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"n: nat" ) ) ).
    c( LogicalAxiom( hof"y0 * y0 < n" ) ).
    b( ImpElimRule( _, _ ) ).
    u( OrIntro2Rule( _, hof"y0 * y0 = s(n)" ) ).
    b( ImpElimRule( _, _ ) ). // end Rewrite <->
    b( AndIntroRule( _, _ ) ).
    u( ExistsIntroRule( _, Dsn ) ).
    qed
  //println( pi4 )

  val pi1 = ProofBuilder.
    c( LogicalAxiom( lem1 ) ).
    u( ForallElimBlock( _, List( le"n:nat", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"n < s(y0) * s(y0) & y0 * y0 <= n" ) ).
    u( AndElim1Rule( _ ) ).
    b( ImpElimRule( _, _ ) ).
    c( pi1Case1 ).
    c( pi1Case2 ).
    t( OrElimRule( _, _, _ ) ).
    qed
  //println( pi1 )

  val pi2Case1 = ProofBuilder.
    // Trans
    c( LogicalAxiom( trans ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(s(y0) * s(y0))", le"s(s(y0)) * s(s(y0))" ) ) ).
    c( LogicalAxiom( lem5 ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"s(n) = s(y0) * s(y0)" ) ).
    b( ImpElimRule( _, _ ) ).
    c( LogicalAxiom( lem4 ) ).
    u( ForallElimRule( _, le"y0: nat" ) ).
    b( AndIntroRule( _, _ ) ).
    b( ImpElimRule( _, _ ) ). // end Trans
    // Rewrite <->
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"s(y0) * s(y0)", le"s(n)" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( symm ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"s(n) = s(y0) * s(y0)" ) ).
    b( ImpElimRule( _, _ ) ).
    u( OrIntro1Rule( _, hof"s(y0) * s(y0) < s(n)" ) ).
    b( ImpElimRule( _, _ ) ). // end Rewrite <->
    b( AndIntroRule( _, _ ) ).
    u( ContractionRule( _, hof"s(n) = s(y0) * s(y0)" ) ).
    u( ExistsIntroRule( _, Dsn ) ).
    qed
  //println( pi32 )

  val pi2Case2 = ProofBuilder.
    c( LogicalAxiom( hof"s(n) < s(y0) * s(y0)" ) ).
    // Rewrite <->
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"s(n)" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( lem5 ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"n:nat" ) ) ).
    c( LogicalAxiom( hof"y0 * y0 = n" ) ).
    b( ImpElimRule( _, _ ) ).
    u( OrIntro2Rule( _, hof"y0 * y0 = s(n)" ) ).
    b( ImpElimRule( _, _ ) ). // end Rewrite <->
    b( AndIntroRule( _, _ ) ).
    u( ExistsIntroRule( _, Dsn ) ).
    qed
  //println( case2 )

  val pi2 = ProofBuilder.
    c( LogicalAxiom( lem1 ) ).
    u( ForallElimBlock( _, List( le"n:nat", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"n < s(y0) * s(y0) & y0 * y0 <= n" ) ).
    u( AndElim1Rule( _ ) ).
    b( ImpElimRule( _, _ ) ).
    c( pi2Case1 ).
    c( pi2Case2 ).
    t( OrElimRule( _, _, _ ) ).
    qed
  //println( pi22 )

  val pi0 = ProofBuilder.
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"n:nat" ) ) ).
    u( AndElim1Rule( _ ) ).
    c( LogicalAxiom( hof"n < s(y0) * s(y0) & y0 * y0 <= n" ) ).
    u( AndElim2Rule( _ ) ).
    b( ImpElimRule( _, _ ) ).
    c( pi2 ).
    c( pi1 ).
    t( OrElimRule( _, _, _ ) ).
    u( ContractionRule( _, hof"n < s(y0) * s(y0) & y0 * y0 <= n" ) ).
    u( ContractionRule( _, hof"n < s(y0) * s(y0) & y0 * y0 <= n" ) ).
    u( ContractionRule( _, lem4 ) ).
    u( ContractionRule( _, lem5 ) ).
    u( ContractionRule( _, defleq ) ).
    u( ContractionRule( _, defleq ) ).
    u( ContractionRule( _, defleq ) ).
    u( ContractionRule( _, defleq ) ).
    u( ContractionRule( _, trans ) ).
    u( ContractionRule( _, symm ) ).
    u( ContractionRule( _, lem1 ) ).
    qed
  //println( pi0 )

  val step = ProofBuilder.
    c( LogicalAxiom( Dn ) ).
    c( pi0 ).
    b( ExistsElimRule( _, _, hov"y0:nat" ) ).
    qed
  //println( step )

  val classicalStep = ProofBuilder.
    c( step ).
    c( LogicalAxiom( -hof"0 = 0" ) ).
    c( LogicalAxiom( hof"0 = 0" ) ).
    b( NegElimRule( _, _ ) ).
    u( BottomElimRule( _, Dsn ) ).
    u( WeakeningRule( _, -Dn ) ).
    u( WeakeningRule( _, Dn ) ).
    b( ExcludedMiddleRule( _, _ ) ).
    qed
  println( classicalStep )

  val icStep = InductionCase( classicalStep, hoc"s", List( classicalStep.endSequent.indexOfInAnt( Dn ) ), List( hov"n:nat" ) )

  val base = ProofBuilder.
    c( LogicalAxiom( peano2 ) ).
    u( ForallElimRule( _, le"s(0)" ) ).
    c( LogicalAxiom( lem8 ) ).
    u( ForallElimRule( _, le"0:nat" ) ).
    b( EqualityElimRule( _, _, hof"0 < x", hov"x:nat" ) ).
    // begin 0 * 0 <= 0
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"0 * 0", le"0:nat" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( peano1 ) ).
    u( ForallElimRule( _, le"0:nat" ) ).
    u( OrIntro1Rule( _, hof"0 * 0 < 0" ) ).
    b( ImpElimRule( _, _ ) ). // end 0 * 0 <= 0
    b( AndIntroRule( _, _ ) ).
    u( ExistsIntroRule( _, D0 ) ).
    qed
  //println( base )
  val icBase = InductionCase( base, hoc"0:nat", List.empty, List.empty )

  val proof = ProofBuilder.
    c( InductionRule( List( icBase, icStep ), Abs( hov"n:nat", Dn ), le"n:nat" ) ).
    u( ForallIntroRule( _, hov"n:nat", hov"n:nat" ) ).
    u( ContractionRule( _, defleq ) ).
    qed
  //println( proof )
  prooftool( proof )
  import extraction.{ ScalaCodeGenerator, FSharpCodeGenerator }
  val m1 = ClassicalExtraction.extractCases( proof )
  ScalaCodeGenerator( m1 )( ClassicalExtraction.systemT( ctx ) )

  val m = MRealizability.mrealize( proof )
  implicit var systemT = MRealizability.systemT( ctx )
  println( "free vars: " + freeVariables( m._2( le"s(s(s(s(0))))" ) ) )
  println( normalize( m._2( le"s(s(s(s(0))))" ) ) )
}

object extractedCorrectAxiomClassicalDifferentEMFormulas extends Script {
  def s( x: Int ) = x + 1
  def mul( x: Int )( y: Int ) = x * y
  def leq( x: Int )( y: Int ) = x <= y

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

  def natRec[A]( p1: A )( p2: ( Int => A => A ) )( p3: Int ): A = {
    if ( p3 == 0 ) {
      p1
    } else {
      p2( p3 - 1 )( natRec( p1 )( p2 )( p3 - 1 ) )
    }
  }

  class NewException[A]( m: A ) extends Exception { def getVal: A = m }
  def exception[A]( p: A ) = { new NewException( p ) }

  def pi1[A, B]( p: ( A, B ) ) = p._1
  def bar[A, B, C]( p2: A => C )( p3: B => C ): C = { ??? }

  def pair[A, B]( p0: A )( p1: B ): Tuple2[A, B] = ( p0, p1 )
  def efq( p: Throwable ) = { throw p }

  val prog = ( {
    v_16: Unit =>
      ( {
        v_15: ( Unit => Exception ) =>
          ( {
            v_13: ( Int => ( Int => ( Unit => Unit ) ) ) =>
              ( {
                v_7: ( Int => ( Int => ( Unit => Unit ) ) ) =>
                  ( {
                    v_9: ( Int => Unit ) =>
                      ( {
                        v_7: ( Int => ( Int => ( Unit => Unit ) ) ) =>
                          ( {
                            v_6: ( Int => ( Int => ( Int => ( Tuple2[Unit, Unit] => Unit ) ) ) ) =>
                              ( {
                                v_10: ( Int => ( Int => ( Unit => Unit ) ) ) =>
                                  ( {
                                    v_5: ( Int => ( Int => ( Unit => Sum[Unit, Unit] ) ) ) =>
                                      ( {
                                        v_2: ( Int => Unit ) =>
                                          ( {
                                            v_0: ( Int => Unit ) =>
                                              ( {
                                                v: ( Int => Unit ) =>
                                                  ( {
                                                    v_1: ( Int => ( Int => Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] ) ) =>
                                                      ( {
                                                        n: Int =>
                                                          natRec( pair( 0 )( pair( () )( pi2( v_1( mul( 0 )( 0 ) )( 0 ) )( inl[Unit, Unit]( v_2( 0 ) ) ) ) ) )( ( {
                                                            n: Int =>
                                                              ( {
                                                                v_3: Tuple2[Int, Tuple2[Unit, Unit]] =>
                                                                  try {
                                                                    ( {
                                                                      v_17: ( Tuple2[Int, Tuple2[Unit, Unit]] => Exception ) => efq( v_15( v_16 ) )
                                                                    } )( exception )
                                                                  } catch {
                                                                    case e: NewException[Tuple2[Int, Tuple2[Unit, Unit]]] => ( {
                                                                      v_3: Tuple2[Int, Tuple2[Unit, Unit]] =>
                                                                        matchSum( pi1( v_1( mul( pi1( v_3 ) )( pi1( v_3 ) ) )( n ) )( pi2( pi2( v_3 ) ) ) )( ( {
                                                                          v_12: Unit =>
                                                                            matchSum( v_5( n )( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( pi1( pi2( v_3 ) ) ) )( ( {
                                                                              v_8: Unit => pair( s( pi1( v_3 ) ) )( pair( v_6( s( n ) )( s( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) ) )( mul( s( s( pi1( v_3 ) ) ) )( s( s( pi1( v_3 ) ) ) ) )( pair( v_7( s( n ) )( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( v_8 ) )( v_9( pi1( v_3 ) ) ) ) )( pi2( v_1( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( s( n ) ) )( inl[Unit, Unit]( v_10( s( n ) )( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( v_8 ) ) ) ) )
                                                                            } ) )( ( {
                                                                              v_11: Unit => pair( pi1( v_3 ) )( pair( v_11 )( pi2( v_1( mul( pi1( v_3 ) )( pi1( v_3 ) ) )( s( n ) ) )( inr[Unit, Unit]( v_7( mul( pi1( v_3 ) )( pi1( v_3 ) ) )( n )( v_12 ) ) ) ) )
                                                                            } ) )
                                                                        } ) )( ( {
                                                                          v_14: Unit =>
                                                                            matchSum( v_5( n )( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( pi1( pi2( v_3 ) ) ) )( ( {
                                                                              v_8: Unit => pair( s( pi1( v_3 ) ) )( pair( v_6( s( n ) )( s( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) ) )( mul( s( s( pi1( v_3 ) ) ) )( s( s( pi1( v_3 ) ) ) ) )( pair( v_7( s( n ) )( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( v_8 ) )( v_9( pi1( v_3 ) ) ) ) )( pi2( v_1( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( s( n ) ) )( inl[Unit, Unit]( v_10( s( n ) )( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( v_8 ) ) ) ) )
                                                                            } ) )( ( {
                                                                              v_11: Unit => pair( pi1( v_3 ) )( pair( v_11 )( pi2( v_1( mul( pi1( v_3 ) )( pi1( v_3 ) ) )( s( n ) ) )( inr[Unit, Unit]( v_13( mul( pi1( v_3 ) )( pi1( v_3 ) ) )( n )( v_14 ) ) ) ) )
                                                                            } ) )
                                                                        } ) )
                                                                    } )( e.getVal )
                                                                    case e => println( "BUG" ); throw e
                                                                  }
                                                              } )
                                                          } ) )( n )
                                                      } )
                                                  } )
                                              } )
                                          } )
                                      } )
                                  } )
                              } )
                          } )
                      } )
                  } )
              } )
          } )
      } )
  } )

  val arg1 = { _: Int => { ( _: Int ) => ( { _: Unit => () } ) } }
  val arg2 = { _: Int => { ( _: Int ) => ( { _: Unit => () } ) } }
  val arg3 = { _: Int =>
    { ( _: Int ) =>
      ( { _: Int =>
        ( { _: Tuple2[Unit, Unit] =>
          ()
        } )
      } )
    }
  }
  // val lem1 = hof"!x!y (x < y -> (s(x) = y | s(x) < y))"
  val arg4 = { x: Int =>
    { ( y: Int ) =>
      ( { _: Unit =>
        {
          //println( s"v_9: $x, $y" )
          if ( s( x ) == y ) {
            //println( "case s(x) == y\n" )
            inl[Unit, Unit]( () )
          } else if ( s( x ) < y ) {
            //println( "case s(x) < y\n" )
            inr[Unit, Unit]( () )
          } else {
            //println( "case s(x) > y\n" )
            // Don't care
            //inl[Unit, Unit]( () )
            inr[Unit, Unit]( () )
          }
        };
      } )
    }
  }
  val arg5 = { _: Int => { ( _: Int ) => ( { _: Unit => () } ) } }
  val arg6 = { _: Int => () }
  val arg7 = { _: Int => { ( _: Int ) => ( { _: Unit => () } ) } }
  val arg9 = { _: Int => () }

  //val defleq = hof"!x!y ((x<=y -> (x=y | x<y))) & ((x=y | x < y) -> x<=y))"

  val arg10 = { x: Int =>
    { ( y: Int ) =>
      ( { _: Unit =>
        //println( s"v_1: $x, $y" )
        /*
inr[Unit, Unit]( () )
*/
        // Don't understand this yet
        if ( x == y ) {
          //println( "case x == y\n" )
          inl[Unit, Unit]( () )
        } else if ( x < y ) {
          //println( "case x < y\n" )
          inr[Unit, Unit]( () )
        } else {
          //println( "case x > y\n" )
          // Don't care
          inr[Unit, Unit]( () )
        }
      }, { _: Sum[Unit, Unit] => () } )
    }
  }
  val arg11 = { _: Int => () }
  val arg12 = { _: Int => () }

  // Exception in thread "main" java.lang.ClassCastException: scala.runtime.BoxedUnit cannot be cast to scala.Tuple2
  // in catch block
  val realProg = prog( () )( exception )( arg1 )( arg2 )( arg11 )( arg5 )( arg3 )( arg5 )( arg4 )( arg11 )( arg11 )( arg12 )( arg10 )

  0 to 4 map ( i => println( s"$i: ${realProg( i )._1}" ) )
  println( "Testing 1000 inputs" )
  0 to 1000 foreach ( i => {
    if ( Math.floor( Math.sqrt( i ) ).toInt != realProg( i )._1 ) {
      throw new Exception( s"realProg failed at input $i." )
    }
  } )
}

object sqrtProofManualCorrectAxiomClassicalDerivationAfterEFQ extends Script {

  import gapt.expr._
  import gapt.formats.babel.{ Notation, Precedence }
  import gapt.proofs.Context
  import gapt.proofs.nd._

  implicit var ctx = Context.default
  ctx += Context.InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += Notation.Infix( "<", Precedence.infixRel )
  ctx += Notation.Infix( "*", Precedence.timesDiv )
  ctx += Notation.Infix( "<=", Precedence.infixRel )
  ctx += hoc"'*': nat>nat>nat"
  ctx += hoc"'<': nat>nat>o"
  ctx += hoc"'<=': nat>nat>o"

  val defleq = hof"!x!y (x<=y <-> (x=y | x<y))"
  val trans = hof"!x!y!z (x<y & y<z -> x<z)"
  val lem1 = hof"!x!y (x < y -> (s(x) = y | s(x) < y))"
  val lem3 = hof"!x!y (x = y -> s(x) = s(y))"
  val lem4 = hof"!x (s(s(x) * s(x)) < s(s(x)) * s(s(x)))"
  val lem5 = hof"!x!y (x = y -> x < s(y))"
  val symm = hof"!(x:nat)!(y:nat) (x = y -> y = x)"
  val lem7 = hof"!x!y (x < y -> x < s(y))"

  val peano1 = hof"!x (0 * x = 0)"
  val peano2 = hof"!x (s(0) * x = x)"
  val lem8 = hof"!x (x < s(x))"

  val D0 = hof"?y (0 < s(y) * s(y) & y * y <= 0)"
  val Dn = hof"?y (n < s(y) * s(y) & y * y <= n)"
  val Dsn = hof"?y (s(n) < s(y) * s(y) & y * y <= s(n))"

  val pi1Case1 = ProofBuilder.
    // Trans
    c( LogicalAxiom( trans ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(s(y0) * s(y0))", le"s(s(y0)) * s(s(y0))" ) ) ).
    c( LogicalAxiom( lem5 ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"s(n) = s(y0) * s(y0)" ) ).
    b( ImpElimRule( _, _ ) ).
    c( LogicalAxiom( lem4 ) ).
    u( ForallElimRule( _, le"y0: nat" ) ).
    b( AndIntroRule( _, _ ) ).
    b( ImpElimRule( _, _ ) ). // end Trans
    // Rewrite <->
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"s(y0) * s(y0)", le"s(n)" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( symm ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"s(n) = s(y0) * s(y0)" ) ).
    b( ImpElimRule( _, _ ) ).
    u( OrIntro1Rule( _, hof"s(y0) * s(y0) < s(n)" ) ).
    b( ImpElimRule( _, _ ) ). // end Rewrite <->
    b( AndIntroRule( _, _ ) ).
    u( ContractionRule( _, hof"s(n) = s(y0) * s(y0)" ) ).
    u( ExistsIntroRule( _, Dsn ) ).
    qed
  //println( pi3 )

  val pi1Case2 = ProofBuilder.
    c( LogicalAxiom( hof"s(n) < s(y0) * s(y0)" ) ).
    // Rewrite <->
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"s(n)" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( lem7 ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"n: nat" ) ) ).
    c( LogicalAxiom( hof"y0 * y0 < n" ) ).
    b( ImpElimRule( _, _ ) ).
    u( OrIntro2Rule( _, hof"y0 * y0 = s(n)" ) ).
    b( ImpElimRule( _, _ ) ). // end Rewrite <->
    b( AndIntroRule( _, _ ) ).
    u( ExistsIntroRule( _, Dsn ) ).
    qed
  //println( pi4 )

  val pi1 = ProofBuilder.
    c( LogicalAxiom( lem1 ) ).
    u( ForallElimBlock( _, List( le"n:nat", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"n < s(y0) * s(y0) & y0 * y0 <= n" ) ).
    u( AndElim1Rule( _ ) ).
    b( ImpElimRule( _, _ ) ).
    c( pi1Case1 ).
    c( pi1Case2 ).
    t( OrElimRule( _, _, _ ) ).
    qed
  //println( pi1 )

  val pi2Case1 = ProofBuilder.
    // Trans
    c( LogicalAxiom( trans ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(s(y0) * s(y0))", le"s(s(y0)) * s(s(y0))" ) ) ).
    c( LogicalAxiom( lem5 ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"s(n) = s(y0) * s(y0)" ) ).
    b( ImpElimRule( _, _ ) ).
    c( LogicalAxiom( lem4 ) ).
    u( ForallElimRule( _, le"y0: nat" ) ).
    b( AndIntroRule( _, _ ) ).
    b( ImpElimRule( _, _ ) ). // end Trans
    // Rewrite <->
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"s(y0) * s(y0)", le"s(n)" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( symm ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"s(n) = s(y0) * s(y0)" ) ).
    b( ImpElimRule( _, _ ) ).
    u( OrIntro1Rule( _, hof"s(y0) * s(y0) < s(n)" ) ).
    b( ImpElimRule( _, _ ) ). // end Rewrite <->
    b( AndIntroRule( _, _ ) ).
    u( ContractionRule( _, hof"s(n) = s(y0) * s(y0)" ) ).
    u( ExistsIntroRule( _, Dsn ) ).
    qed
  //println( pi32 )

  val pi2Case2 = ProofBuilder.
    c( LogicalAxiom( hof"s(n) < s(y0) * s(y0)" ) ).
    // Rewrite <->
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"s(n)" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( lem5 ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"n:nat" ) ) ).
    c( LogicalAxiom( hof"y0 * y0 = n" ) ).
    b( ImpElimRule( _, _ ) ).
    u( OrIntro2Rule( _, hof"y0 * y0 = s(n)" ) ).
    b( ImpElimRule( _, _ ) ). // end Rewrite <->
    b( AndIntroRule( _, _ ) ).
    u( ExistsIntroRule( _, Dsn ) ).
    qed
  //println( case2 )

  val pi2 = ProofBuilder.
    c( LogicalAxiom( lem1 ) ).
    u( ForallElimBlock( _, List( le"n:nat", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"n < s(y0) * s(y0) & y0 * y0 <= n" ) ).
    u( AndElim1Rule( _ ) ).
    b( ImpElimRule( _, _ ) ).
    c( pi2Case1 ).
    c( pi2Case2 ).
    t( OrElimRule( _, _, _ ) ).
    qed
  //println( pi22 )

  val pi0 = ProofBuilder.
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"n:nat" ) ) ).
    u( AndElim1Rule( _ ) ).
    c( LogicalAxiom( hof"n < s(y0) * s(y0) & y0 * y0 <= n" ) ).
    u( AndElim2Rule( _ ) ).
    b( ImpElimRule( _, _ ) ).
    c( pi2 ).
    c( pi1 ).
    t( OrElimRule( _, _, _ ) ).
    u( ContractionRule( _, hof"n < s(y0) * s(y0) & y0 * y0 <= n" ) ).
    u( ContractionRule( _, hof"n < s(y0) * s(y0) & y0 * y0 <= n" ) ).
    u( ContractionRule( _, lem4 ) ).
    u( ContractionRule( _, lem5 ) ).
    u( ContractionRule( _, defleq ) ).
    u( ContractionRule( _, defleq ) ).
    u( ContractionRule( _, defleq ) ).
    u( ContractionRule( _, defleq ) ).
    u( ContractionRule( _, trans ) ).
    u( ContractionRule( _, symm ) ).
    u( ContractionRule( _, lem1 ) ).
    qed
  //println( pi0 )

  val step = ProofBuilder.
    c( LogicalAxiom( Dn ) ).
    c( pi0 ).
    b( ExistsElimRule( _, _, hov"y0:nat" ) ).
    qed
  //println( step )

  val classicalStep = ProofBuilder.
    c( step ).
    c( LogicalAxiom( -Dn ) ).
    c( LogicalAxiom( Dn ) ).
    b( NegElimRule( _, _ ) ).
    u( BottomElimRule( _, Dn ) ).
    c( pi0 ).
    b( ExistsElimRule( _, _, hov"y0:nat" ) ).
    b( ExcludedMiddleRule( _, _ ) ).
    qed
  println( classicalStep )

  val icStep = InductionCase( classicalStep, hoc"s", List( classicalStep.endSequent.indexOfInAnt( Dn ) ), List( hov"n:nat" ) )

  val base = ProofBuilder.
    c( LogicalAxiom( peano2 ) ).
    u( ForallElimRule( _, le"s(0)" ) ).
    c( LogicalAxiom( lem8 ) ).
    u( ForallElimRule( _, le"0:nat" ) ).
    b( EqualityElimRule( _, _, hof"0 < x", hov"x:nat" ) ).
    // begin 0 * 0 <= 0
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"0 * 0", le"0:nat" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( peano1 ) ).
    u( ForallElimRule( _, le"0:nat" ) ).
    u( OrIntro1Rule( _, hof"0 * 0 < 0" ) ).
    b( ImpElimRule( _, _ ) ). // end 0 * 0 <= 0
    b( AndIntroRule( _, _ ) ).
    u( ExistsIntroRule( _, D0 ) ).
    qed
  //println( base )
  val icBase = InductionCase( base, hoc"0:nat", List.empty, List.empty )

  val proof = ProofBuilder.
    c( InductionRule( List( icBase, icStep ), Abs( hov"n:nat", Dn ), le"n:nat" ) ).
    u( ForallIntroRule( _, hov"n:nat", hov"n:nat" ) ).
    u( ContractionRule( _, defleq ) ).
    qed
  //println( proof )
  prooftool( proof )
  import extraction.{ ScalaCodeGenerator, FSharpCodeGenerator }
  val m1 = ClassicalExtraction.extractCases( proof )
  ScalaCodeGenerator( m1 )( ClassicalExtraction.systemT( ctx ) )

  val m = MRealizability.mrealize( proof )
  implicit var systemT = MRealizability.systemT( ctx )
  println( "free vars: " + freeVariables( m._2( le"s(s(s(s(0))))" ) ) )
  println( normalize( m._2( le"s(s(s(s(0))))" ) ) )
}

object extractedCorrectAxiomClassicalDerivationAfterEFQ extends Script {
  def s( x: Int ) = x + 1
  def mul( x: Int )( y: Int ) = x * y
  def leq( x: Int )( y: Int ) = x <= y

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

  def natRec[A]( p1: A )( p2: ( Int => A => A ) )( p3: Int ): A = {
    if ( p3 == 0 ) {
      p1
    } else {
      p2( p3 - 1 )( natRec( p1 )( p2 )( p3 - 1 ) )
    }
  }

  class NewException[A]( m: A ) extends Exception { def getVal: A = m }
  def exception[A]( p: A ) = { new NewException( p ) }

  def pi1[A, B]( p: ( A, B ) ) = p._1
  def bar[A, B, C]( p2: A => C )( p3: B => C ): C = { ??? }

  def pair[A, B]( p0: A )( p1: B ): Tuple2[A, B] = ( p0, p1 )
  def efq( p: Throwable ) = { throw p }

  val prog = ( {
    v_13: ( Int => ( Int => ( Unit => Unit ) ) ) =>
      ( {
        v_7: ( Int => ( Int => ( Unit => Unit ) ) ) =>
          ( {
            v_9: ( Int => Unit ) =>
              ( {
                v_7: ( Int => ( Int => ( Unit => Unit ) ) ) =>
                  ( {
                    v_1: ( Int => ( Int => Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] ) ) =>
                      ( {
                        v_6: ( Int => ( Int => ( Int => ( Tuple2[Unit, Unit] => Unit ) ) ) ) =>
                          ( {
                            v_10: ( Int => ( Int => ( Unit => Unit ) ) ) =>
                              ( {
                                v_5: ( Int => ( Int => ( Unit => Sum[Unit, Unit] ) ) ) =>
                                  ( {
                                    v_13: ( Int => ( Int => ( Unit => Unit ) ) ) =>
                                      ( {
                                        v_7: ( Int => ( Int => ( Unit => Unit ) ) ) =>
                                          ( {
                                            v_9: ( Int => Unit ) =>
                                              ( {
                                                v_7: ( Int => ( Int => ( Unit => Unit ) ) ) =>
                                                  ( {
                                                    v_6: ( Int => ( Int => ( Int => ( Tuple2[Unit, Unit] => Unit ) ) ) ) =>
                                                      ( {
                                                        v_10: ( Int => ( Int => ( Unit => Unit ) ) ) =>
                                                          ( {
                                                            v_5: ( Int => ( Int => ( Unit => Sum[Unit, Unit] ) ) ) =>
                                                              ( {
                                                                v_2: ( Int => Unit ) =>
                                                                  ( {
                                                                    v_0: ( Int => Unit ) =>
                                                                      ( {
                                                                        v: ( Int => Unit ) =>
                                                                          ( {
                                                                            v_1: ( Int => ( Int => Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] ) ) =>
                                                                              ( {
                                                                                n: Int =>
                                                                                  natRec( pair( 0 )( pair( () )( pi2( v_1( mul( 0 )( 0 ) )( 0 ) )( inl[Unit, Unit]( v_2( 0 ) ) ) ) ) )( ( {
                                                                                    n: Int =>
                                                                                      ( {
                                                                                        v_3: Tuple2[Int, Tuple2[Unit, Unit]] =>
                                                                                          try {
                                                                                            matchSum( pi1( v_1( mul( pi1( efq( exception( v_3 ) ) ) )( pi1( efq( exception( v_3 ) ) ) ) )( n ) )( pi2( pi2( efq( exception( v_3 ) ) ) ) ) )( ( {
                                                                                              v_12: Unit =>
                                                                                                matchSum( v_5( n )( mul( s( pi1( efq( exception( v_3 ) ) ) ) )( s( pi1( efq( exception( v_3 ) ) ) ) ) )( pi1( pi2( efq( exception( v_3 ) ) ) ) ) )( ( {
                                                                                                  v_8: Unit => pair( s( pi1( efq( exception( v_3 ) ) ) ) )( pair( v_6( s( n ) )( s( mul( s( pi1( efq( exception( v_3 ) ) ) ) )( s( pi1( efq( exception( v_3 ) ) ) ) ) ) )( mul( s( s( pi1( efq( exception( v_3 ) ) ) ) ) )( s( s( pi1( efq( exception( v_3 ) ) ) ) ) ) )( pair( v_7( s( n ) )( mul( s( pi1( efq( exception( v_3 ) ) ) ) )( s( pi1( efq( exception( v_3 ) ) ) ) ) )( v_8 ) )( v_9( pi1( efq( exception( v_3 ) ) ) ) ) ) )( pi2( v_1( mul( s( pi1( efq( exception( v_3 ) ) ) ) )( s( pi1( efq( exception( v_3 ) ) ) ) ) )( s( n ) ) )( inl[Unit, Unit]( v_10( s( n ) )( mul( s( pi1( efq( exception( v_3 ) ) ) ) )( s( pi1( efq( exception( v_3 ) ) ) ) ) )( v_8 ) ) ) ) )
                                                                                                } ) )( ( {
                                                                                                  v_11: Unit => pair( pi1( efq( exception( v_3 ) ) ) )( pair( v_11 )( pi2( v_1( mul( pi1( efq( exception( v_3 ) ) ) )( pi1( efq( exception( v_3 ) ) ) ) )( s( n ) ) )( inr[Unit, Unit]( v_7( mul( pi1( efq( exception( v_3 ) ) ) )( pi1( efq( exception( v_3 ) ) ) ) )( n )( v_12 ) ) ) ) )
                                                                                                } ) )
                                                                                            } ) )( ( {
                                                                                              v_14: Unit =>
                                                                                                matchSum( v_5( n )( mul( s( pi1( efq( exception( v_3 ) ) ) ) )( s( pi1( efq( exception( v_3 ) ) ) ) ) )( pi1( pi2( efq( exception( v_3 ) ) ) ) ) )( ( {
                                                                                                  v_8: Unit => pair( s( pi1( efq( exception( v_3 ) ) ) ) )( pair( v_6( s( n ) )( s( mul( s( pi1( efq( exception( v_3 ) ) ) ) )( s( pi1( efq( exception( v_3 ) ) ) ) ) ) )( mul( s( s( pi1( efq( exception( v_3 ) ) ) ) ) )( s( s( pi1( efq( exception( v_3 ) ) ) ) ) ) )( pair( v_7( s( n ) )( mul( s( pi1( efq( exception( v_3 ) ) ) ) )( s( pi1( efq( exception( v_3 ) ) ) ) ) )( v_8 ) )( v_9( pi1( efq( exception( v_3 ) ) ) ) ) ) )( pi2( v_1( mul( s( pi1( efq( exception( v_3 ) ) ) ) )( s( pi1( efq( exception( v_3 ) ) ) ) ) )( s( n ) ) )( inl[Unit, Unit]( v_10( s( n ) )( mul( s( pi1( efq( exception( v_3 ) ) ) ) )( s( pi1( efq( exception( v_3 ) ) ) ) ) )( v_8 ) ) ) ) )
                                                                                                } ) )( ( {
                                                                                                  v_11: Unit => pair( pi1( efq( exception( v_3 ) ) ) )( pair( v_11 )( pi2( v_1( mul( pi1( efq( exception( v_3 ) ) ) )( pi1( efq( exception( v_3 ) ) ) ) )( s( n ) ) )( inr[Unit, Unit]( v_13( mul( pi1( efq( exception( v_3 ) ) ) )( pi1( efq( exception( v_3 ) ) ) ) )( n )( v_14 ) ) ) ) )
                                                                                                } ) )
                                                                                            } ) )
                                                                                          } catch {
                                                                                            case e: NewException[Tuple2[Int, Tuple2[Unit, Unit]]] => ( {
                                                                                              v_3: Tuple2[Int, Tuple2[Unit, Unit]] =>
                                                                                                matchSum( pi1( v_1( mul( pi1( v_3 ) )( pi1( v_3 ) ) )( n ) )( pi2( pi2( v_3 ) ) ) )( ( {
                                                                                                  v_12: Unit =>
                                                                                                    matchSum( v_5( n )( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( pi1( pi2( v_3 ) ) ) )( ( {
                                                                                                      v_8: Unit => pair( s( pi1( v_3 ) ) )( pair( v_6( s( n ) )( s( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) ) )( mul( s( s( pi1( v_3 ) ) ) )( s( s( pi1( v_3 ) ) ) ) )( pair( v_7( s( n ) )( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( v_8 ) )( v_9( pi1( v_3 ) ) ) ) )( pi2( v_1( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( s( n ) ) )( inl[Unit, Unit]( v_10( s( n ) )( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( v_8 ) ) ) ) )
                                                                                                    } ) )( ( {
                                                                                                      v_11: Unit => pair( pi1( v_3 ) )( pair( v_11 )( pi2( v_1( mul( pi1( v_3 ) )( pi1( v_3 ) ) )( s( n ) ) )( inr[Unit, Unit]( v_7( mul( pi1( v_3 ) )( pi1( v_3 ) ) )( n )( v_12 ) ) ) ) )
                                                                                                    } ) )
                                                                                                } ) )( ( {
                                                                                                  v_14: Unit =>
                                                                                                    matchSum( v_5( n )( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( pi1( pi2( v_3 ) ) ) )( ( {
                                                                                                      v_8: Unit => pair( s( pi1( v_3 ) ) )( pair( v_6( s( n ) )( s( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) ) )( mul( s( s( pi1( v_3 ) ) ) )( s( s( pi1( v_3 ) ) ) ) )( pair( v_7( s( n ) )( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( v_8 ) )( v_9( pi1( v_3 ) ) ) ) )( pi2( v_1( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( s( n ) ) )( inl[Unit, Unit]( v_10( s( n ) )( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( v_8 ) ) ) ) )
                                                                                                    } ) )( ( {
                                                                                                      v_11: Unit => pair( pi1( v_3 ) )( pair( v_11 )( pi2( v_1( mul( pi1( v_3 ) )( pi1( v_3 ) ) )( s( n ) ) )( inr[Unit, Unit]( v_13( mul( pi1( v_3 ) )( pi1( v_3 ) ) )( n )( v_14 ) ) ) ) )
                                                                                                    } ) )
                                                                                                } ) )
                                                                                            } )( e.getVal )
                                                                                            case e => println( "BUG" ); throw e
                                                                                          }
                                                                                      } )
                                                                                  } ) )( n )
                                                                              } )
                                                                          } )
                                                                      } )
                                                                  } )
                                                              } )
                                                          } )
                                                      } )
                                                  } )
                                              } )
                                          } )
                                      } )
                                  } )
                              } )
                          } )
                      } )
                  } )
              } )
          } )
      } )
  } )

  val arg1 = { _: Int => { ( _: Int ) => ( { _: Unit => () } ) } }
  val arg2 = { _: Int => { ( _: Int ) => ( { _: Unit => () } ) } }
  val arg3 = { _: Int =>
    { ( _: Int ) =>
      ( { _: Int =>
        ( { _: Tuple2[Unit, Unit] =>
          ()
        } )
      } )
    }
  }
  // val lem1 = hof"!x!y (x < y -> (s(x) = y | s(x) < y))"
  val arg4 = { x: Int =>
    { ( y: Int ) =>
      ( { _: Unit =>
        {
          //println( s"v_9: $x, $y" )
          if ( s( x ) == y ) {
            //println( "case s(x) == y\n" )
            inl[Unit, Unit]( () )
          } else if ( s( x ) < y ) {
            //println( "case s(x) < y\n" )
            inr[Unit, Unit]( () )
          } else {
            //println( "case s(x) > y\n" )
            // Don't care
            //inl[Unit, Unit]( () )
            inr[Unit, Unit]( () )
          }
        };
      } )
    }
  }
  val arg5 = { _: Int => { ( _: Int ) => ( { _: Unit => () } ) } }
  val arg6 = { _: Int => () }
  val arg7 = { _: Int => { ( _: Int ) => ( { _: Unit => () } ) } }
  val arg9 = { _: Int => () }

  //val defleq = hof"!x!y ((x<=y -> (x=y | x<y))) & ((x=y | x < y) -> x<=y))"

  val arg10 = { x: Int =>
    { ( y: Int ) =>
      ( { _: Unit =>
        //println( s"v_1: $x, $y" )
        /*
inr[Unit, Unit]( () )
*/
        // Don't understand this yet
        if ( x == y ) {
          //println( "case x == y\n" )
          inl[Unit, Unit]( () )
        } else if ( x < y ) {
          //println( "case x < y\n" )
          inr[Unit, Unit]( () )
        } else {
          //println( "case x > y\n" )
          // Don't care
          inr[Unit, Unit]( () )
        }
      }, { _: Sum[Unit, Unit] => () } )
    }
  }
  val arg11 = { _: Int => () }
  val arg12 = { _: Int => () }

  // Exception in thread "main" java.lang.ClassCastException: scala.runtime.BoxedUnit cannot be cast to scala.Tuple2
  // in catch block
  val realProg = prog( arg1 )( arg2 )( arg11 )( arg5 )( arg10 )( arg3 )( arg5 )( arg4 )( arg5 )( arg5 )( arg11 )( arg5 )( arg3 )( arg5 )( arg4 )( arg11 )( arg11 )( arg11 )( arg10 )

  0 to 4 map ( i => println( s"$i: ${realProg( i )._1}" ) )
  println( "Testing 1000 inputs" )
  0 to 1000 foreach ( i => {
    if ( Math.floor( Math.sqrt( i ) ).toInt != realProg( i )._1 ) {
      throw new Exception( s"realProg failed at input $i." )
    }
  } )
}

object sqrtProofManualCorrectAxiomClassicalDifferentEMFormulasUsingEFQ extends Script {

  import gapt.expr._
  import gapt.formats.babel.{ Notation, Precedence }
  import gapt.proofs.Context
  import gapt.proofs.nd._

  implicit var ctx = Context.default
  ctx += Context.InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += Notation.Infix( "<", Precedence.infixRel )
  ctx += Notation.Infix( "*", Precedence.timesDiv )
  ctx += Notation.Infix( "<=", Precedence.infixRel )
  ctx += hoc"'*': nat>nat>nat"
  ctx += hoc"'<': nat>nat>o"
  ctx += hoc"'<=': nat>nat>o"

  val defleq = hof"!x!y (x<=y <-> (x=y | x<y))"
  val trans = hof"!x!y!z (x<y & y<z -> x<z)"
  val lem1 = hof"!x!y (x < y -> (s(x) = y | s(x) < y))"
  val lem3 = hof"!x!y (x = y -> s(x) = s(y))"
  val lem4 = hof"!x (s(s(x) * s(x)) < s(s(x)) * s(s(x)))"
  val lem5 = hof"!x!y (x = y -> x < s(y))"
  val symm = hof"!(x:nat)!(y:nat) (x = y -> y = x)"
  val lem7 = hof"!x!y (x < y -> x < s(y))"

  val peano1 = hof"!x (0 * x = 0)"
  val peano2 = hof"!x (s(0) * x = x)"
  val lem8 = hof"!x (x < s(x))"

  val D0 = hof"?y (0 < s(y) * s(y) & y * y <= 0)"
  val Dn = hof"?y (n < s(y) * s(y) & y * y <= n)"
  val Dsn = hof"?y (s(n) < s(y) * s(y) & y * y <= s(n))"

  val pi1Case1 = ProofBuilder.
    // Trans
    c( LogicalAxiom( trans ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(s(y0) * s(y0))", le"s(s(y0)) * s(s(y0))" ) ) ).
    c( LogicalAxiom( lem5 ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"s(n) = s(y0) * s(y0)" ) ).
    b( ImpElimRule( _, _ ) ).
    c( LogicalAxiom( lem4 ) ).
    u( ForallElimRule( _, le"y0: nat" ) ).
    b( AndIntroRule( _, _ ) ).
    b( ImpElimRule( _, _ ) ). // end Trans
    // Rewrite <->
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"s(y0) * s(y0)", le"s(n)" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( symm ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"s(n) = s(y0) * s(y0)" ) ).
    b( ImpElimRule( _, _ ) ).
    u( OrIntro1Rule( _, hof"s(y0) * s(y0) < s(n)" ) ).
    b( ImpElimRule( _, _ ) ). // end Rewrite <->
    b( AndIntroRule( _, _ ) ).
    u( ContractionRule( _, hof"s(n) = s(y0) * s(y0)" ) ).
    u( ExistsIntroRule( _, Dsn ) ).
    qed
  //println( pi3 )

  val pi1Case2 = ProofBuilder.
    c( LogicalAxiom( hof"s(n) < s(y0) * s(y0)" ) ).
    // Rewrite <->
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"s(n)" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( lem7 ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"n: nat" ) ) ).
    c( LogicalAxiom( hof"y0 * y0 < n" ) ).
    b( ImpElimRule( _, _ ) ).
    u( OrIntro2Rule( _, hof"y0 * y0 = s(n)" ) ).
    b( ImpElimRule( _, _ ) ). // end Rewrite <->
    b( AndIntroRule( _, _ ) ).
    u( ExistsIntroRule( _, Dsn ) ).
    qed
  //println( pi4 )

  val pi1 = ProofBuilder.
    c( LogicalAxiom( lem1 ) ).
    u( ForallElimBlock( _, List( le"n:nat", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"n < s(y0) * s(y0) & y0 * y0 <= n" ) ).
    u( AndElim1Rule( _ ) ).
    b( ImpElimRule( _, _ ) ).
    c( pi1Case1 ).
    c( pi1Case2 ).
    t( OrElimRule( _, _, _ ) ).
    qed
  //println( pi1 )

  val pi2Case1 = ProofBuilder.
    // Trans
    c( LogicalAxiom( trans ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(s(y0) * s(y0))", le"s(s(y0)) * s(s(y0))" ) ) ).
    c( LogicalAxiom( lem5 ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"s(n) = s(y0) * s(y0)" ) ).
    b( ImpElimRule( _, _ ) ).
    c( LogicalAxiom( lem4 ) ).
    u( ForallElimRule( _, le"y0: nat" ) ).
    b( AndIntroRule( _, _ ) ).
    b( ImpElimRule( _, _ ) ). // end Trans
    // Rewrite <->
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"s(y0) * s(y0)", le"s(n)" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( symm ) ).
    u( ForallElimBlock( _, List( le"s(n)", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"s(n) = s(y0) * s(y0)" ) ).
    b( ImpElimRule( _, _ ) ).
    u( OrIntro1Rule( _, hof"s(y0) * s(y0) < s(n)" ) ).
    b( ImpElimRule( _, _ ) ). // end Rewrite <->
    b( AndIntroRule( _, _ ) ).
    u( ContractionRule( _, hof"s(n) = s(y0) * s(y0)" ) ).
    u( ExistsIntroRule( _, Dsn ) ).
    qed
  //println( pi32 )

  val pi2Case2 = ProofBuilder.
    c( LogicalAxiom( hof"s(n) < s(y0) * s(y0)" ) ).
    // Rewrite <->
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"s(n)" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( lem5 ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"n:nat" ) ) ).
    c( LogicalAxiom( hof"y0 * y0 = n" ) ).
    b( ImpElimRule( _, _ ) ).
    u( OrIntro2Rule( _, hof"y0 * y0 = s(n)" ) ).
    b( ImpElimRule( _, _ ) ). // end Rewrite <->
    b( AndIntroRule( _, _ ) ).
    u( ExistsIntroRule( _, Dsn ) ).
    qed
  //println( case2 )

  val pi2 = ProofBuilder.
    c( LogicalAxiom( lem1 ) ).
    u( ForallElimBlock( _, List( le"n:nat", le"s(y0) * s(y0)" ) ) ).
    c( LogicalAxiom( hof"n < s(y0) * s(y0) & y0 * y0 <= n" ) ).
    u( AndElim1Rule( _ ) ).
    b( ImpElimRule( _, _ ) ).
    c( pi2Case1 ).
    c( pi2Case2 ).
    t( OrElimRule( _, _, _ ) ).
    qed
  //println( pi22 )

  val pi0 = ProofBuilder.
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"y0 * y0", le"n:nat" ) ) ).
    u( AndElim1Rule( _ ) ).
    c( LogicalAxiom( hof"n < s(y0) * s(y0) & y0 * y0 <= n" ) ).
    u( AndElim2Rule( _ ) ).
    b( ImpElimRule( _, _ ) ).
    c( pi2 ).
    c( pi1 ).
    t( OrElimRule( _, _, _ ) ).
    u( ContractionRule( _, hof"n < s(y0) * s(y0) & y0 * y0 <= n" ) ).
    u( ContractionRule( _, hof"n < s(y0) * s(y0) & y0 * y0 <= n" ) ).
    u( ContractionRule( _, lem4 ) ).
    u( ContractionRule( _, lem5 ) ).
    u( ContractionRule( _, defleq ) ).
    u( ContractionRule( _, defleq ) ).
    u( ContractionRule( _, defleq ) ).
    u( ContractionRule( _, defleq ) ).
    u( ContractionRule( _, trans ) ).
    u( ContractionRule( _, symm ) ).
    u( ContractionRule( _, lem1 ) ).
    qed
  //println( pi0 )

  val step = ProofBuilder.
    c( LogicalAxiom( Dn ) ).
    c( pi0 ).
    b( ExistsElimRule( _, _, hov"y0:nat" ) ).
    qed
  //println( step )

  val classicalStep = ProofBuilder.
    c( step ).
    c( LogicalAxiom( -Dn ) ).
    c( LogicalAxiom( -hof"0 = 0" ) ).
    c( LogicalAxiom( hof"0 = 0" ) ).
    b( NegElimRule( _, _ ) ).
    u( BottomElimRule( _, Dn ) ).
    b( NegElimRule( _, _ ) ).
    u( BottomElimRule( _, -Dn ) ).
    c( LogicalAxiom( Dn ) ).
    b( NegElimRule( _, _ ) ).
    u( BottomElimRule( _, Dsn ) ).
    b( ExcludedMiddleRule( _, _ ) ).
    qed

  //println( classicalStep )
  //prooftool( classicalStep )

  val icStep = InductionCase( classicalStep, hoc"s", List( classicalStep.endSequent.indexOfInAnt( Dn ) ), List( hov"n:nat" ) )

  val base = ProofBuilder.
    c( LogicalAxiom( peano2 ) ).
    u( ForallElimRule( _, le"s(0)" ) ).
    c( LogicalAxiom( lem8 ) ).
    u( ForallElimRule( _, le"0:nat" ) ).
    b( EqualityElimRule( _, _, hof"0 < x", hov"x:nat" ) ).
    // begin 0 * 0 <= 0
    c( LogicalAxiom( defleq ) ).
    u( ForallElimBlock( _, List( le"0 * 0", le"0:nat" ) ) ).
    u( AndElim2Rule( _ ) ).
    c( LogicalAxiom( peano1 ) ).
    u( ForallElimRule( _, le"0:nat" ) ).
    u( OrIntro1Rule( _, hof"0 * 0 < 0" ) ).
    b( ImpElimRule( _, _ ) ). // end 0 * 0 <= 0
    b( AndIntroRule( _, _ ) ).
    u( ExistsIntroRule( _, D0 ) ).
    qed
  //println( base )
  val icBase = InductionCase( base, hoc"0:nat", List.empty, List.empty )

  val proof = ProofBuilder.
    c( InductionRule( List( icBase, icStep ), Abs( hov"n:nat", Dn ), le"n:nat" ) ).
    u( ForallIntroRule( _, hov"n:nat", hov"n:nat" ) ).
    u( ContractionRule( _, defleq ) ).
    qed
  //println( proof )
  prooftool( proof )
  import extraction.{ ScalaCodeGenerator, FSharpCodeGenerator }
  val m1 = ClassicalExtraction.extractCases( proof )
  ScalaCodeGenerator( m1 )( ClassicalExtraction.systemT( ctx ) )

  val m = MRealizability.mrealize( proof )
  implicit var systemT = MRealizability.systemT( ctx )
  println( "free vars: " + freeVariables( m._2( le"s(s(s(s(0))))" ) ) )
  println( normalize( m._2( le"s(s(s(s(0))))" ) ) )
}

object extractedCorrectAxiomClassicalDifferentEMFormulasUsingEFQ extends Script {
  def s( x: Int ) = x + 1
  def mul( x: Int )( y: Int ) = x * y
  def leq( x: Int )( y: Int ) = x <= y

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

  def natRec[A]( p1: A )( p2: ( Int => A => A ) )( p3: Int ): A = {
    if ( p3 == 0 ) {
      p1
    } else {
      p2( p3 - 1 )( natRec( p1 )( p2 )( p3 - 1 ) )
    }
  }

  case class NewException[A]( m: A ) extends Exception
  def exception[A]( p: A ) = { new NewException( p ) }

  def pi1[A, B]( p: ( A, B ) ) = p._1
  def bar[A, B, C]( p2: A => C )( p3: B => C ): C = { ??? }

  def pair[A, B]( p0: A )( p1: B ): Tuple2[A, B] = ( p0, p1 )
  def efq[B]( p: Throwable ): B = { throw p }

  val prog = ( {
    v_17: Unit =>
      ( {
        v_16: ( Unit => Exception ) =>
          ( {
            v_13: ( Int => ( Int => ( Unit => Unit ) ) ) =>
              ( {
                v_7: ( Int => ( Int => ( Unit => Unit ) ) ) =>
                  ( {
                    v_9: ( Int => Unit ) =>
                      ( {
                        v_7: ( Int => ( Int => ( Unit => Unit ) ) ) =>
                          ( {
                            v_6: ( Int => ( Int => ( Int => ( Tuple2[Unit, Unit] => Unit ) ) ) ) =>
                              ( {
                                v_10: ( Int => ( Int => ( Unit => Unit ) ) ) =>
                                  ( {
                                    v_5: ( Int => ( Int => ( Unit => Sum[Unit, Unit] ) ) ) =>
                                      ( {
                                        v_2: ( Int => Unit ) =>
                                          ( {
                                            v_0: ( Int => Unit ) =>
                                              ( {
                                                v: ( Int => Unit ) =>
                                                  ( {
                                                    v_1: ( Int => ( Int => Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] ) ) =>
                                                      ( {
                                                        n: Int =>
                                                          natRec( pair( 0 )( pair( () )( pi2( v_1( mul( 0 )( 0 ) )( 0 ) )( inl[Unit, Unit]( v_2( 0 ) ) ) ) ) )( ( {
                                                            n: Int =>
                                                              ( {
                                                                v_3: Tuple2[Int, Tuple2[Unit, Unit]] =>
                                                                  try {
                                                                    ( {
                                                                      v_15: ( Tuple2[Int, Tuple2[Unit, Unit]] => Exception ) => efq[Tuple2[Int, Tuple2[Unit, Unit]]]( efq[( Tuple2[Int, Tuple2[Unit, Unit]] => Exception )]( v_15( efq[Tuple2[Int, Tuple2[Unit, Unit]]]( v_16( v_17 ) ) ) )( v_3 ) )
                                                                    } )( exception )
                                                                  } catch {
                                                                    case NewException( exceptionValue: Tuple2[Int, Tuple2[Unit, Unit]] ) => ( {
                                                                      v_3: Tuple2[Int, Tuple2[Unit, Unit]] =>
                                                                        matchSum( pi1( v_1( mul( pi1( v_3 ) )( pi1( v_3 ) ) )( n ) )( pi2( pi2( v_3 ) ) ) )( ( {
                                                                          v_12: Unit =>
                                                                            matchSum( v_5( n )( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( pi1( pi2( v_3 ) ) ) )( ( {
                                                                              v_8: Unit => pair( s( pi1( v_3 ) ) )( pair( v_6( s( n ) )( s( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) ) )( mul( s( s( pi1( v_3 ) ) ) )( s( s( pi1( v_3 ) ) ) ) )( pair( v_7( s( n ) )( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( v_8 ) )( v_9( pi1( v_3 ) ) ) ) )( pi2( v_1( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( s( n ) ) )( inl[Unit, Unit]( v_10( s( n ) )( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( v_8 ) ) ) ) )
                                                                            } ) )( ( {
                                                                              v_11: Unit => pair( pi1( v_3 ) )( pair( v_11 )( pi2( v_1( mul( pi1( v_3 ) )( pi1( v_3 ) ) )( s( n ) ) )( inr[Unit, Unit]( v_7( mul( pi1( v_3 ) )( pi1( v_3 ) ) )( n )( v_12 ) ) ) ) )
                                                                            } ) )
                                                                        } ) )( ( {
                                                                          v_14: Unit =>
                                                                            matchSum( v_5( n )( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( pi1( pi2( v_3 ) ) ) )( ( {
                                                                              v_8: Unit => pair( s( pi1( v_3 ) ) )( pair( v_6( s( n ) )( s( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) ) )( mul( s( s( pi1( v_3 ) ) ) )( s( s( pi1( v_3 ) ) ) ) )( pair( v_7( s( n ) )( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( v_8 ) )( v_9( pi1( v_3 ) ) ) ) )( pi2( v_1( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( s( n ) ) )( inl[Unit, Unit]( v_10( s( n ) )( mul( s( pi1( v_3 ) ) )( s( pi1( v_3 ) ) ) )( v_8 ) ) ) ) )
                                                                            } ) )( ( {
                                                                              v_11: Unit => pair( pi1( v_3 ) )( pair( v_11 )( pi2( v_1( mul( pi1( v_3 ) )( pi1( v_3 ) ) )( s( n ) ) )( inr[Unit, Unit]( v_13( mul( pi1( v_3 ) )( pi1( v_3 ) ) )( n )( v_14 ) ) ) ) )
                                                                            } ) )
                                                                        } ) )
                                                                    } )( exceptionValue )
                                                                    case e => println( "BUG" ); throw e
                                                                  }
                                                              } )
                                                          } ) )( n )
                                                      } )
                                                  } )
                                              } )
                                          } )
                                      } )
                                  } )
                              } )
                          } )
                      } )
                  } )
              } )
          } )
      } )
  } )

  val arg1 = { _: Int => { ( _: Int ) => ( { _: Unit => () } ) } }
  val arg2 = { _: Int => { ( _: Int ) => ( { _: Unit => () } ) } }
  val arg3 = { _: Int =>
    { ( _: Int ) =>
      ( { _: Int =>
        ( { _: Tuple2[Unit, Unit] =>
          ()
        } )
      } )
    }
  }
  // val lem1 = hof"!x!y (x < y -> (s(x) = y | s(x) < y))"
  val arg4 = { x: Int =>
    { ( y: Int ) =>
      ( { _: Unit =>
        {
          //println( s"v_9: $x, $y" )
          if ( s( x ) == y ) {
            //println( "case s(x) == y\n" )
            inl[Unit, Unit]( () )
          } else if ( s( x ) < y ) {
            //println( "case s(x) < y\n" )
            inr[Unit, Unit]( () )
          } else {
            //println( "case s(x) > y\n" )
            // Don't care
            //inl[Unit, Unit]( () )
            inr[Unit, Unit]( () )
          }
        };
      } )
    }
  }
  val arg5 = { _: Int => { ( _: Int ) => ( { _: Unit => () } ) } }
  val arg6 = { _: Int => () }
  val arg7 = { _: Int => { ( _: Int ) => ( { _: Unit => () } ) } }
  val arg9 = { _: Int => () }

  //val defleq = hof"!x!y ((x<=y -> (x=y | x<y))) & ((x=y | x < y) -> x<=y))"

  val arg10 = { x: Int =>
    { ( y: Int ) =>
      ( { _: Unit =>
        //println( s"v_1: $x, $y" )
        /*
inr[Unit, Unit]( () )
*/
        // Don't understand this yet
        if ( x == y ) {
          //println( "case x == y\n" )
          inl[Unit, Unit]( () )
        } else if ( x < y ) {
          //println( "case x < y\n" )
          inr[Unit, Unit]( () )
        } else {
          //println( "case x > y\n" )
          // Don't care
          inr[Unit, Unit]( () )
        }
      }, { _: Sum[Unit, Unit] => () } )
    }
  }
  val arg11 = { _: Int => () }
  val arg12 = { _: Int => () }

  // Exception in thread "main" java.lang.ClassCastException: scala.runtime.BoxedUnit cannot be cast to scala.Tuple2
  // in catch block
  val realProg = prog( () )( exception )( arg1 )( arg2 )( arg11 )( arg5 )( arg3 )( arg5 )( arg4 )( arg11 )( arg11 )( arg12 )( arg10 )

  0 to 4 map ( i => println( s"$i: ${realProg( i )._1}" ) )
  println( "Testing 1000 inputs" )
  0 to 1000 foreach ( i => {
    if ( Math.floor( Math.sqrt( i ) ).toInt != realProg( i )._1 ) {
      throw new Exception( s"realProg failed at input $i." )
    }
  } )
}

object exceptionTest extends Script {
  case class NewException[A]( m: A ) extends Exception
  try {
    throw new NewException( 5 )
  } catch {
    case NewException( v: String ) => println( "string: " + v )
    case NewException( v )         => println( v )
    case e                         => println( e.getMessage )
  }
}

object automaticProof extends Script {
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

  def natRec[A]( p1: A )( p2: ( Int => A => A ) )( p3: Int ): A = {
    if ( p3 == 0 ) {
      p1
    } else {
      p2( p3 - 1 )( natRec( p1 )( p2 )( p3 - 1 ) )
    }
  }

  case class NewException[A]( m: A ) extends Exception

  def exception[A]( p: A ) = {
    new NewException( p )
  }

  def pi1[A, B]( p: ( A, B ) ) = p._1

  def bar[A, B, C]( p2: A => C )( p3: B => C ): C = {
    ???
  }

  def pair[A, B]( p0: A )( p1: B ): Tuple2[A, B] = ( p0, p1 )

  def efq[B]( p: Throwable ): B = {
    throw p
  }

  val prog = ( {
    v_69: ( Int => Unit ) =>
      ( {
        v_68: ( Int => Unit ) =>
          ( {
            v_64: ( Int => ( Int => ( Unit => Unit ) ) ) =>
              ( {
                v_62: ( Int => ( Int => ( Int => ( Tuple2[Unit, Unit] => Unit ) ) ) ) =>
                  ( {
                    v_59: ( Int => ( Int => ( Unit => Sum[Unit, Unit] ) ) ) =>
                      ( {
                        v_53: ( Int => Unit ) =>
                          ( {
                            v_52: ( Int => Unit ) =>
                              ( {
                                v_57: ( Int => ( Int => Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] ) ) =>
                                  ( {
                                    v_2: Int =>
                                      natRec( pair( 0 )( pair( () )( () ) ) )( ( {
                                        v_0: Int =>
                                          ( {
                                            v_8: Tuple2[Int, Tuple2[Unit, Unit]] =>
                                              try {
                                                ( {
                                                  v_11: ( Tuple2[Int, Tuple2[Unit, Unit]] => Exception ) =>
                                                    pair( pi1( v_8 ) )(
                                                      try {
                                                        ( {
                                                          v_13: ( Tuple2[Unit, Unit] => Exception ) =>
                                                            efq[Tuple2[Unit, Unit]]( v_11( pair( s( pi1( v_8 ) ) )(
                                                              try {
                                                                ( {
                                                                  v_14: ( Tuple2[Unit, Unit] => Exception ) =>
                                                                    efq[Tuple2[Unit, Unit]]( v_13(
                                                                      try {
                                                                        ( {
                                                                          v_13: ( Tuple2[Unit, Unit] => Exception ) =>
                                                                            try {
                                                                              ( {
                                                                                v_13: ( Tuple2[Unit, Unit] => Exception ) =>
                                                                                  efq[Tuple2[Unit, Unit]]( v_14( pair(
                                                                                    try {
                                                                                      ( {
                                                                                        v_17: ( Unit => Exception ) =>
                                                                                          efq[Unit]( v_13( pair( matchSum( v_59( v_0 )( mul( s( pi1( v_8 ) ) )( s( pi1( v_8 ) ) ) )( pi1( pi2( v_8 ) ) ) )( ( {
                                                                                            v_18: Unit => efq[Unit]( v_17( () ) )
                                                                                          } ) )( ( {
                                                                                            v_23: Unit => v_23
                                                                                          } ) ) )(
                                                                                            try {
                                                                                              ( {
                                                                                                v_28: ( Unit => Exception ) =>
                                                                                                  matchSum( pi1( v_57( mul( pi1( v_8 ) )( pi1( v_8 ) ) )( v_0 ) )( pi2( pi2( v_8 ) ) ) )( ( {
                                                                                                    v_29: Unit => efq[Unit]( v_28( () ) )
                                                                                                  } ) )( ( {
                                                                                                    v_36: Unit => pi2( v_57( mul( pi1( v_8 ) )( pi1( v_8 ) ) )( s( v_0 ) ) )( inr[Unit, Unit]( v_64( mul( pi1( v_8 ) )( pi1( v_8 ) ) )( v_0 )( v_36 ) ) )
                                                                                                  } ) )
                                                                                              } )( exception )
                                                                                            } catch {
                                                                                              case NewException( exceptionValue: Unit ) => ( {
                                                                                                v_26: Unit => v_26
                                                                                              } )( exceptionValue )
                                                                                              case e => println( "BUG" ); throw e
                                                                                            } ) ) )
                                                                                      } )( exception )
                                                                                    } catch {
                                                                                      case NewException( exceptionValue: Unit ) => ( {
                                                                                        v_15: Unit => v_15
                                                                                      } )( exceptionValue )
                                                                                      case e => println( "BUG" ); throw e
                                                                                    } )(
                                                                                      try {
                                                                                        ( {
                                                                                          v_40: ( Unit => Exception ) =>
                                                                                            efq[Unit]( v_13( pair( matchSum( v_59( v_0 )( mul( s( pi1( v_8 ) ) )( s( pi1( v_8 ) ) ) )( pi1( pi2( v_8 ) ) ) )( ( {
                                                                                              v_18: Unit => efq[Unit]( v_40( () ) )
                                                                                            } ) )( ( {
                                                                                              v_23: Unit => v_23
                                                                                            } ) ) )(
                                                                                              try {
                                                                                                ( {
                                                                                                  v_28: ( Unit => Exception ) =>
                                                                                                    matchSum( pi1( v_57( mul( pi1( v_8 ) )( pi1( v_8 ) ) )( v_0 ) )( pi2( pi2( v_8 ) ) ) )( ( {
                                                                                                      v_29: Unit => efq[Unit]( v_28( () ) )
                                                                                                    } ) )( ( {
                                                                                                      v_36: Unit => pi2( v_57( mul( pi1( v_8 ) )( pi1( v_8 ) ) )( s( v_0 ) ) )( inr[Unit, Unit]( v_64( mul( pi1( v_8 ) )( pi1( v_8 ) ) )( v_0 )( v_36 ) ) )
                                                                                                    } ) )
                                                                                                } )( exception )
                                                                                              } catch {
                                                                                                case NewException( exceptionValue: Unit ) => ( {
                                                                                                  v_26: Unit => v_26
                                                                                                } )( exceptionValue )
                                                                                                case e => println( "BUG" ); throw e
                                                                                              } ) ) )
                                                                                        } )( exception )
                                                                                      } catch {
                                                                                        case NewException( exceptionValue: Unit ) => ( {
                                                                                          v_39: Unit => v_39
                                                                                        } )( exceptionValue )
                                                                                        case e => println( "BUG" ); throw e
                                                                                      } ) ) )
                                                                              } )( exception )
                                                                            } catch {
                                                                              case NewException( exceptionValue: Tuple2[Unit, Unit] ) => ( {
                                                                                v_10: Tuple2[Unit, Unit] => v_10
                                                                              } )( exceptionValue )
                                                                              case e => println( "BUG" ); throw e
                                                                            }
                                                                        } )( exception )
                                                                      } catch {
                                                                        case NewException( exceptionValue: Tuple2[Unit, Unit] ) => ( {
                                                                          v_10: Tuple2[Unit, Unit] => v_10
                                                                        } )( exceptionValue )
                                                                        case e => println( "BUG" ); throw e
                                                                      } ) )
                                                                } )( exception )
                                                              } catch {
                                                                case NewException( exceptionValue: Tuple2[Unit, Unit] ) => ( {
                                                                  v_12: Tuple2[Unit, Unit] => v_12
                                                                } )( exceptionValue )
                                                                case e => println( "BUG" ); throw e
                                                              } ) ) )
                                                        } )( exception )
                                                      } catch {
                                                        case NewException( exceptionValue: Tuple2[Unit, Unit] ) => ( {
                                                          v_10: Tuple2[Unit, Unit] => v_10
                                                        } )( exceptionValue )
                                                        case e => println( "BUG" ); throw e
                                                      } )
                                                } )( exception )
                                              } catch {
                                                case NewException( exceptionValue: Tuple2[Int, Tuple2[Unit, Unit]] ) => ( {
                                                  v_9: Tuple2[Int, Tuple2[Unit, Unit]] => v_9
                                                } )( exceptionValue )
                                                case e => println( "BUG" ); throw e
                                              }
                                          } )
                                      } ) )( v_2 )
                                  } )
                              } )
                          } )
                      } )
                  } )
              } )
          } )
      } )
  } )

  val arg1 = { _: Int => () }
  val arg2 = { _: Int => { _: Int => { _: Unit => () } } }
  val arg3 = { _: Int => { _: Int => { _: Int => { _: Tuple2[Unit, Unit] => () } } } }
  val arg4 = { x: Int =>
    { ( y: Int ) =>
      ( { _: Unit =>
        {
          //println( s"v_9: $x, $y" )
          if ( s( x ) == y ) {
            //println( "case s(x) == y\n" )
            inl[Unit, Unit]( () )
          } else if ( s( x ) < y ) {
            //println( "case s(x) < y\n" )
            inr[Unit, Unit]( () )
          } else {
            //println( "case s(x) > y\n" )
            // Don't care
            //inl[Unit, Unit]( () )
            inr[Unit, Unit]( () )
          }
        };
      } )
    }
  }
  val arg10 = { x: Int =>
    { ( y: Int ) =>
      ( { _: Unit =>
        //println( s"v_1: $x, $y" )
        /*
  inr[Unit, Unit]( () )
  */
        // Don't understand this yet
        if ( x == y ) {
          //println( "case x == y\n" )
          inl[Unit, Unit]( () )
        } else if ( x < y ) {
          //println( "case x < y\n" )
          inr[Unit, Unit]( () )
        } else {
          //println( "case x > y\n" )
          // Don't care
          inr[Unit, Unit]( () )
        }
      }, { _: Sum[Unit, Unit] => () } )
    }
  }

  val realProg = prog( arg1 )( arg1 )( arg2 )( arg3 )( arg4 )( arg1 )( arg1 )( arg10 )
  println( realProg( 4 ) )

}
