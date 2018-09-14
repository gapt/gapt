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

object extractedCorrectAxiomClassical extends Script {
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
  def exception[A]( m: A ) = { new NewException( m ) }

  def pi1[A, B]( p: ( A, B ) ) = p._1

  def pair[A, B]( p0: A )( p1: B ): Tuple2[A, B] = ( p0, p1 )
  def efq[B]( p: Throwable ): B = { throw p }
  import shapeless._
  val `NewException[Tuple2[Int, Tuple2[Unit, Unit]]]` = TypeCase[NewException[Tuple2[Int, Tuple2[Unit, Unit]]]]
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
                                                          try {
                                                            ( {
                                                              v_15: ( Tuple2[Int, Tuple2[Unit, Unit]] => Exception ) => efq[Tuple2[Int, Tuple2[Unit, Unit]]]( v_15( v_3 ) )
                                                            } )( exception[Tuple2[Int, Tuple2[Unit, Unit]]] )
                                                          } catch {
                                                            case `NewException[Tuple2[Int, Tuple2[Unit, Unit]]]`( e ) => ( {
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
                                                            } )( e.m )
                                                            case e => println( "BUG 0" ); throw e
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

  def matchSum[A, B, C]( p1: Sum[A, B] )( p2: A => C )( p3: B => C )( implicit debug: Boolean = false ) = {
    p1 match {
      case Inl( a: A ) => {
        if ( debug ) {
          println( s"a: $a" )
        }
        p2( a )
      }
      case Inr( b: B ) => {
        if ( debug ) {
          println( s"b: $b" )
        }
        p3( b )
      }
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
                                                                                          // TODO pi1(p2(v_8)) is () in first run here and then 1 in second
                                                                                          // both of type Int and Unit
                                                                                          println( s"v8: $v_8, pi1(v8): ${pi1( v_8 )}, pi1(pi2(v8)): ${pi1( pi2( v_8 ) )}" )
                                                                                          println( s"before pi1pi2" )
                                                                                          val pi1pi2: Unit = pi1( pi2( v_8 ) )
                                                                                          println( s"pi1pi2: $pi1pi2" )
                                                                                          println( "before matchSum arg" )
                                                                                          println( s"matchSum arg: ${v_59( v_0 )( mul( s( pi1( v_8 ) ) )( s( pi1( v_8 ) ) ) )( pi1( pi2( v_8 ) ) )}" )
                                                                                          println( "after matchSum arg" )
                                                                                          efq[Unit]( v_13( pair( matchSum( v_59( v_0 )( mul( s( pi1( v_8 ) ) )( s( pi1( v_8 ) ) ) )( pi1( pi2( v_8 ) ) ) )( ( {
                                                                                            v_18: Unit => println( "debuginl 1" ); efq[Unit]( v_17( () ) )
                                                                                          } ) )( ( {
                                                                                            v_23: Unit => v_23
                                                                                          } ) )( true ) )(
                                                                                            try {
                                                                                              ( {
                                                                                                v_28: ( Unit => Exception ) =>
                                                                                                  matchSum( pi1( v_57( mul( pi1( v_8 ) )( pi1( v_8 ) ) )( v_0 ) )( pi2( pi2( v_8 ) ) ) )( ( {
                                                                                                    v_29: Unit => efq[Unit]( v_28( () ) )
                                                                                                  } ) )( ( {
                                                                                                    v_36: Unit => pi2( v_57( mul( pi1( v_8 ) )( pi1( v_8 ) ) )( s( v_0 ) ) )( inr[Unit, Unit]( v_64( mul( pi1( v_8 ) )( pi1( v_8 ) ) )( v_0 )( v_36 ) ) )
                                                                                                  } ) )
                                                                                              } )( exception[Unit] )
                                                                                            } catch {
                                                                                              case NewException( exceptionValue: Unit ) => ( {
                                                                                                v_26: Unit => v_26
                                                                                              } )( exceptionValue )
                                                                                              case e => println( s"BUG1 ${e.getMessage()}" ); throw e
                                                                                            } ) ) )
                                                                                      } )( exception[Unit] )
                                                                                    } catch {
                                                                                      case NewException( exceptionValue: Unit ) => ( {
                                                                                        v_15: Unit => { println( "debugcatch 1" ); v_15 }
                                                                                      } )( exceptionValue )
                                                                                      case e => println( s"BUG2 ${e.getMessage()}" ); throw e
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
                                                                                                case e => println( s"BUG3 ${e.getMessage()}" ); throw e
                                                                                              } ) ) )
                                                                                        } )( exception )
                                                                                      } catch {
                                                                                        case NewException( exceptionValue: Unit ) => ( {
                                                                                          v_39: Unit => v_39
                                                                                        } )( exceptionValue )
                                                                                        case e => println( s"BUG4 ${e.getMessage()}" ); throw e
                                                                                      } ) ) )
                                                                              } )( exception )
                                                                            } catch {
                                                                              case NewException( exceptionValue: Tuple2[Unit, Unit] ) => ( {
                                                                                v_10: Tuple2[Unit, Unit] => println( "debugcatch 2" ); v_10
                                                                              } )( exceptionValue )
                                                                              case e => println( s"BUG5 ${e.getMessage()}" ); throw e
                                                                            }
                                                                        } )( exception )
                                                                      } catch {
                                                                        case NewException( exceptionValue: Tuple2[Unit, Unit] ) => ( {
                                                                          v_10: Tuple2[Unit, Unit] => v_10
                                                                        } )( exceptionValue )
                                                                        case e => println( s"BUG6 ${e.getMessage()}" ); throw e
                                                                      } ) )
                                                                } )( exception )
                                                              } catch {
                                                                case NewException( exceptionValue: Tuple2[Unit, Unit] ) => ( {
                                                                  v_12: Tuple2[Unit, Unit] => v_12
                                                                } )( exceptionValue )
                                                                case e => println( s"BUG7 ${e.getMessage()}" ); throw e
                                                              } ) ) )
                                                        } )( exception )
                                                      } catch {
                                                        case NewException( exceptionValue: Tuple2[Unit, Unit] ) => ( {
                                                          v_10: Tuple2[Unit, Unit] => v_10
                                                        } )( exceptionValue )
                                                        case e => println( s"BUG8 ${e.getMessage()}" ); throw e
                                                      } )
                                                } )( exception )
                                              } catch {
                                                case NewException( exceptionValue: Tuple2[Int, Tuple2[Unit, Unit]] ) => ( {
                                                  v_9: Tuple2[Int, Tuple2[Unit, Unit]] => v_9
                                                } )( exceptionValue )
                                                case e => println( s"BUG9 ${e.getMessage()}" ); throw e
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
        println( s"v_59: x=$x, y=$y" )
        if ( s( x ) == y ) {
          inl[Unit, Unit]( () )
        } else if ( s( x ) < y ) {
          inr[Unit, Unit]( () )
        } else {
          // Don't care
          inr[Unit, Unit]( () )
        }
      } )
    }
  }
  val arg10 = { x: Int =>
    { ( y: Int ) =>
      ( { _: Unit =>
        //println( s"v: x=$x, y=$y" )
        if ( x == y ) {
          inl[Unit, Unit]( () )
        } else if ( x < y ) {
          inr[Unit, Unit]( () )
        } else {
          // Don't care
          inr[Unit, Unit]( () )
        }
      }, { _: Sum[Unit, Unit] => () } )
    }
  }

  val realProg = prog( arg1 )( arg1 )( arg2 )( arg3 )( arg4 )( arg1 )( arg1 )( arg10 )
  println( realProg( 4 ) )

}

object automaticProofWithTypeParams extends Script {
  def s( x: Int ) = x + 1

  def mul( x: Int )( y: Int ) = x * y

  def leq( x: Int )( y: Int ) = x <= y

  def pow2( x: Int ) = x * x

  def pi2[A, B]( p: ( A, B ) ): B = p._2

  sealed trait Sum[A, B]

  final case class Inr[A, B]( v: B ) extends Sum[A, B]

  def inr[A, B]( v: B ): Sum[A, B] = new Inr( v )

  def matchSum[A, B, C]( p1: Sum[A, B] )( p2: A => C )( p3: B => C )( implicit debug: Boolean = false ) = {
    p1 match {
      case Inl( a: A ) => {
        if ( debug ) {
          println( s"a: $a" )
        }
        p2( a )
      }
      case Inr( b: B ) => {
        if ( debug ) {
          println( s"b: $b" )
        }
        p3( b )
      }
    }
  }

  def eq[X]( x: X )( y: X ) = x == y

  def lt( x: Int )( y: Int ) = x < y

  final case class Inl[A, B]( v: A ) extends Sum[A, B]

  def inl[A, B]( v: A ): Sum[A, B] = new Inl( v )

  def natRec[A]( p1: A )( p2: ( Int => A => A ) )( p3: Int ): A = {
    if ( p3 == 0 ) {
      val retVal: A = p1
      println( s"in natRec, retVal = $retVal" )
      retVal
    } else {
      val retVal: A = p2( p3 - 1 )( natRec[A]( p1 )( p2 )( p3 - 1 ) )
      println( s"in natRec, retVal = $retVal" )
      retVal
    }
  }

  case class NewException[A]( m: A ) extends Exception

  def exception[A]( p: A ) = {
    new NewException( p )
  }

  def pi1[A, B]( p: ( A, B ) ): A = p._1

  def pair[A, B]( p0: A )( p1: B )( implicit callSite: Int = -1 ): Tuple2[A, B] = {
    println( s"pairing: p0: $p0, p1: $p1 @ callsite $callSite" )
    ( p0, p1 )
  }

  def efq[B]( p: Throwable )( implicit callSite: String = "callsite undef" ): B = {
    p match {
      case NewException( m: Tuple2[Int, Tuple2[Unit, Unit]] ) => println( s"@ $callSite: m = $m CASE 1" )
      case NewException( m: Tuple2[Unit, Unit] ) => println( s"@ $callSite: m = $m CASE 2" )
      case _ => println( s"@ $callSite: OTHER CASE" )
    }
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
                                      ( {
                                        v_3: Unit =>
                                          ( {
                                            v_5: Unit =>
                                              ( {
                                                v_67: ( Int => Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] ) =>
                                                  ( {
                                                    v_66: Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] =>
                                                      ( {
                                                        v_4: Unit =>
                                                          ( {
                                                            v_7: ( Sum[Unit, Unit] => Unit ) =>
                                                              ( {
                                                                v_65: ( Unit => Sum[Unit, Unit] ) =>
                                                                  ( {
                                                                    v_1: ( Int => Tuple2[Int, Tuple2[Unit, Unit]] ) =>
                                                                      ( {
                                                                        v: Tuple2[Int, Tuple2[Unit, Unit]] => v
                                                                      } )( v_1( v_2 ) )
                                                                  } )( ( {
                                                                    n: Int =>
                                                                      natRec[Tuple2[Int, Tuple2[Unit, Unit]]]( pair[Int, Tuple2[Unit, Unit]]( 0 )( pair[Unit, Unit]( () )( ( {
                                                                        v_6: Unit => ()
                                                                      } )( v_7( inl[Unit, Unit]( () ) ) ) )( 7 ) )( 0 ) )( ( {
                                                                        v_0: Int =>
                                                                          ( {
                                                                            v_8: Tuple2[Int, Tuple2[Unit, Unit]] =>
                                                                              println( s"@begin step v_8: $v_8" )
                                                                              val ret: ( Int, ( Unit, Unit ) ) = ( {
                                                                                v_63: ( Int => ( Unit => Unit ) ) =>
                                                                                  ( {
                                                                                    v_35: ( Unit => Unit ) =>
                                                                                      ( {
                                                                                        v_61: ( Int => ( Int => ( Tuple2[Unit, Unit] => Unit ) ) ) =>
                                                                                          ( {
                                                                                            v_60: ( Int => ( Tuple2[Unit, Unit] => Unit ) ) =>
                                                                                              ( {
                                                                                                v_20: ( Tuple2[Unit, Unit] => Unit ) =>
                                                                                                  ( {
                                                                                                    v_58: ( Int => ( Unit => Sum[Unit, Unit] ) ) =>
                                                                                                      ( {
                                                                                                        v_24: ( Unit => Sum[Unit, Unit] ) =>
                                                                                                          ( {
                                                                                                            v_54: ( Int => Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] ) =>
                                                                                                              ( {
                                                                                                                v_55: ( Int => Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] ) =>
                                                                                                                  ( {
                                                                                                                    v_56: ( Int => Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] ) =>
                                                                                                                      ( {
                                                                                                                        v_50: Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] =>
                                                                                                                          ( {
                                                                                                                            v_48: Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] =>
                                                                                                                              ( {
                                                                                                                                v_46: Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] =>
                                                                                                                                  ( {
                                                                                                                                    v_44: Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] =>
                                                                                                                                      ( {
                                                                                                                                        v_22: Unit =>
                                                                                                                                          ( {
                                                                                                                                            v_21: Unit =>
                                                                                                                                              ( {
                                                                                                                                                v_32: Unit =>
                                                                                                                                                  try {
                                                                                                                                                    ( {
                                                                                                                                                      v_11: ( Tuple2[Int, Tuple2[Unit, Unit]] => Exception ) =>
                                                                                                                                                        pair[Int, Tuple2[Unit, Unit]]( { val res = pi1[Int, Tuple2[Unit, Unit]]( v_8 ); println( s"v_8: $v_8, pi1(v_8): $res" ); res } )( {
                                                                                                                                                          val ret: ( Unit, Unit ) = try {
                                                                                                                                                            ( {
                                                                                                                                                              v_13: ( Tuple2[Unit, Unit] => Exception ) =>
                                                                                                                                                                efq[Tuple2[Unit, Unit]]( v_11( pair[Int, Tuple2[Unit, Unit]]( s( { val res = pi1[Int, Tuple2[Unit, Unit]]( v_8 ); println( s"v_8: $v_8, pi1(v_8): $res" ); res } ) )( ( {
                                                                                                                                                                  v_38: Unit =>
                                                                                                                                                                    ( {
                                                                                                                                                                      v_25: Unit =>
                                                                                                                                                                        ( {
                                                                                                                                                                          v_31: ( Sum[Unit, Unit] => Unit ) =>
                                                                                                                                                                            ( {
                                                                                                                                                                              v_49: ( Unit => Sum[Unit, Unit] ) =>
                                                                                                                                                                                ( {
                                                                                                                                                                                  v_33: ( Sum[Unit, Unit] => Unit ) =>
                                                                                                                                                                                    ( {
                                                                                                                                                                                      v_47: ( Unit => Sum[Unit, Unit] ) =>
                                                                                                                                                                                        ( {
                                                                                                                                                                                          v_45: ( Sum[Unit, Unit] => Unit ) =>
                                                                                                                                                                                            ( {
                                                                                                                                                                                              v_37: ( Unit => Sum[Unit, Unit] ) =>
                                                                                                                                                                                                ( {
                                                                                                                                                                                                  v_42: ( Sum[Unit, Unit] => Unit ) =>
                                                                                                                                                                                                    ( {
                                                                                                                                                                                                      v_43: ( Unit => Sum[Unit, Unit] ) =>
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
                                                                                                                                                                                                                            efq[Tuple2[Unit, Unit]]( v_14( pair[Unit, Unit](
                                                                                                                                                                                                                              try {
                                                                                                                                                                                                                                ( {
                                                                                                                                                                                                                                  v_17: ( Unit => Exception ) =>
                                                                                                                                                                                                                                    efq[Unit]( v_13( pair[Unit, Unit]( ( {
                                                                                                                                                                                                                                      v_16: Sum[Unit, Unit] =>
                                                                                                                                                                                                                                        matchSum( v_16 )( ( {
                                                                                                                                                                                                                                          v_18: Unit =>
                                                                                                                                                                                                                                            efq[Unit]( v_17( ( {
                                                                                                                                                                                                                                              v_19: Unit =>
                                                                                                                                                                                                                                                ( {
                                                                                                                                                                                                                                                  v_15: Unit => v_15
                                                                                                                                                                                                                                                } )( () )
                                                                                                                                                                                                                                            } )( v_20( pair[Unit, Unit]( v_21 )( v_22 )( 5 ) ) ) ) )( "efq callsite 4" )
                                                                                                                                                                                                                                        } ) )( ( {
                                                                                                                                                                                                                                          v_23: Unit => v_23
                                                                                                                                                                                                                                        } ) )
                                                                                                                                                                                                                                    } )( v_24( v_25 ) ) )( ( {
                                                                                                                                                                                                                                      v_27: Sum[Unit, Unit] =>
                                                                                                                                                                                                                                        try {
                                                                                                                                                                                                                                          ( {
                                                                                                                                                                                                                                            v_28: ( Unit => Exception ) =>
                                                                                                                                                                                                                                              matchSum( v_27 )( ( {
                                                                                                                                                                                                                                                v_29: Unit =>
                                                                                                                                                                                                                                                  efq[Unit]( v_28( ( {
                                                                                                                                                                                                                                                    v_30: Unit => ()
                                                                                                                                                                                                                                                  } )( v_31( inr[Unit, Unit]( v_32 ) ) ) ) )
                                                                                                                                                                                                                                              } ) )( ( {
                                                                                                                                                                                                                                                v_36: Unit =>
                                                                                                                                                                                                                                                  ( {
                                                                                                                                                                                                                                                    v_26: Unit => v_26
                                                                                                                                                                                                                                                  } )( v_33( inr[Unit, Unit]( ( {
                                                                                                                                                                                                                                                    v_34: Unit => v_34
                                                                                                                                                                                                                                                  } )( v_35( v_36 ) ) ) ) )
                                                                                                                                                                                                                                              } ) )
                                                                                                                                                                                                                                          } )( exception[Unit] )
                                                                                                                                                                                                                                        } catch {
                                                                                                                                                                                                                                          case NewException( exceptionValue: Unit ) => ( {
                                                                                                                                                                                                                                            v_26: Unit => v_26
                                                                                                                                                                                                                                          } )( exceptionValue )
                                                                                                                                                                                                                                          case e => println( "BUG" ); throw e
                                                                                                                                                                                                                                        }
                                                                                                                                                                                                                                    } )( v_37( v_38 ) ) )( 6 ) ) )( "efq callsite 3" )
                                                                                                                                                                                                                                } )( exception[Unit] )
                                                                                                                                                                                                                              } catch {
                                                                                                                                                                                                                                case NewException( exceptionValue: Unit ) => ( {
                                                                                                                                                                                                                                  v_15: Unit => v_15
                                                                                                                                                                                                                                } )( exceptionValue )
                                                                                                                                                                                                                                case e => println( "BUG" ); throw e
                                                                                                                                                                                                                              } )(
                                                                                                                                                                                                                                try {
                                                                                                                                                                                                                                  ( {
                                                                                                                                                                                                                                    v_40: ( Unit => Exception ) =>
                                                                                                                                                                                                                                      efq[Unit]( v_13( pair[Unit, Unit]( ( {
                                                                                                                                                                                                                                        v_41: Unit =>
                                                                                                                                                                                                                                          ( {
                                                                                                                                                                                                                                            v_16: Sum[Unit, Unit] =>
                                                                                                                                                                                                                                              matchSum( v_16 )( ( {
                                                                                                                                                                                                                                                v_18: Unit => efq[Unit]( v_40( () ) )
                                                                                                                                                                                                                                              } ) )( ( {
                                                                                                                                                                                                                                                v_23: Unit => v_23
                                                                                                                                                                                                                                              } ) )
                                                                                                                                                                                                                                          } )( v_24( v_25 ) )
                                                                                                                                                                                                                                      } )( v_42( inl[Unit, Unit]( () ) ) ) )( ( {
                                                                                                                                                                                                                                        v_27: Sum[Unit, Unit] =>
                                                                                                                                                                                                                                          try {
                                                                                                                                                                                                                                            ( {
                                                                                                                                                                                                                                              v_28: ( Unit => Exception ) =>
                                                                                                                                                                                                                                                matchSum( v_27 )( ( {
                                                                                                                                                                                                                                                  v_29: Unit =>
                                                                                                                                                                                                                                                    efq[Unit]( v_28( ( {
                                                                                                                                                                                                                                                      v_30: Unit => ()
                                                                                                                                                                                                                                                    } )( v_31( inr[Unit, Unit]( v_32 ) ) ) ) )
                                                                                                                                                                                                                                                } ) )( ( {
                                                                                                                                                                                                                                                  v_36: Unit =>
                                                                                                                                                                                                                                                    ( {
                                                                                                                                                                                                                                                      v_26: Unit => v_26
                                                                                                                                                                                                                                                    } )( v_33( inr[Unit, Unit]( ( {
                                                                                                                                                                                                                                                      v_34: Unit => v_34
                                                                                                                                                                                                                                                    } )( v_35( v_36 ) ) ) ) )
                                                                                                                                                                                                                                                } ) )
                                                                                                                                                                                                                                            } )( exception[Unit] )
                                                                                                                                                                                                                                          } catch {
                                                                                                                                                                                                                                            case NewException( exceptionValue: Unit ) => ( {
                                                                                                                                                                                                                                              v_26: Unit => v_26
                                                                                                                                                                                                                                            } )( exceptionValue )
                                                                                                                                                                                                                                            case e => println( "BUG" ); throw e
                                                                                                                                                                                                                                          }
                                                                                                                                                                                                                                      } )( v_37( v_38 ) ) )( 4 ) ) )
                                                                                                                                                                                                                                  } )( exception[Unit] )
                                                                                                                                                                                                                                } catch {
                                                                                                                                                                                                                                  case NewException( exceptionValue: Unit ) => ( {
                                                                                                                                                                                                                                    v_39: Unit => v_39
                                                                                                                                                                                                                                  } )( exceptionValue )
                                                                                                                                                                                                                                  case e => println( "BUG" ); throw e
                                                                                                                                                                                                                                } )( 3 ) ) )( "efq callsite 2" )
                                                                                                                                                                                                                        } )( exception[Tuple2[Unit, Unit]] )
                                                                                                                                                                                                                      } catch {
                                                                                                                                                                                                                        case NewException( exceptionValue: Tuple2[Unit, Unit] ) => ( {
                                                                                                                                                                                                                          v_10: Tuple2[Unit, Unit] => v_10
                                                                                                                                                                                                                        } )( exceptionValue )
                                                                                                                                                                                                                        case e => println( "BUG" ); throw e
                                                                                                                                                                                                                      }
                                                                                                                                                                                                                  } )( exception[Tuple2[Unit, Unit]] )
                                                                                                                                                                                                                } catch {
                                                                                                                                                                                                                  case NewException( exceptionValue: Tuple2[Unit, Unit] ) => ( {
                                                                                                                                                                                                                    v_10: Tuple2[Unit, Unit] => v_10
                                                                                                                                                                                                                  } )( exceptionValue )
                                                                                                                                                                                                                  case e => println( "BUG" ); throw e
                                                                                                                                                                                                                } ) )( "efq callsite 1" )
                                                                                                                                                                                                          } )( exception[Tuple2[Unit, Unit]] )
                                                                                                                                                                                                        } catch {
                                                                                                                                                                                                          case NewException( exceptionValue: Tuple2[Unit, Unit] ) => ( {
                                                                                                                                                                                                            v_12: Tuple2[Unit, Unit] => v_12
                                                                                                                                                                                                          } )( exceptionValue )
                                                                                                                                                                                                          case e => println( "BUG" ); throw e
                                                                                                                                                                                                        }
                                                                                                                                                                                                    } )( pi1[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_44 ) )
                                                                                                                                                                                                } )( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_44 ) )
                                                                                                                                                                                            } )( pi1[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_46 ) )
                                                                                                                                                                                        } )( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_46 ) )
                                                                                                                                                                                    } )( pi1[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_48 ) )
                                                                                                                                                                                } )( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_48 ) )
                                                                                                                                                                            } )( pi1[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_50 ) )
                                                                                                                                                                        } )( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_50 ) )
                                                                                                                                                                    } )( pi1[Unit, Unit]( pi2[Int, Tuple2[Unit, Unit]]( { println( s"1: v_8: $v_8" ); v_8 } ) ) )
                                                                                                                                                                } )( pi2[Unit, Unit]( pi2[Int, Tuple2[Unit, Unit]]( { println( s"2: v_8: $v_8" ); v_8 } ) ) ) )( 2 ) ) )( "efq callsite 0" )
                                                                                                                                                            } )( exception[Tuple2[Unit, Unit]] )
                                                                                                                                                          } catch {
                                                                                                                                                            case NewException( exceptionValue: Tuple2[Unit, Unit] ) =>
                                                                                                                                                              println( s"exceptionValue: $exceptionValue" ); ( {
                                                                                                                                                                v_10: Tuple2[Unit, Unit] => v_10
                                                                                                                                                              } )( exceptionValue )
                                                                                                                                                            case e => println( "BUG" ); throw e
                                                                                                                                                          }
                                                                                                                                                          println( s"ret at callsite 1 = $ret" ); ret
                                                                                                                                                        } )( 1 )
                                                                                                                                                    } )( exception[Tuple2[Int, Tuple2[Unit, Unit]]] )
                                                                                                                                                  } catch {
                                                                                                                                                    case NewException( exceptionValue: Tuple2[Int, Tuple2[Unit, Unit]] ) => ( {
                                                                                                                                                      v_9: Tuple2[Int, Tuple2[Unit, Unit]] => v_9
                                                                                                                                                    } )( exceptionValue )
                                                                                                                                                    case e => println( "BUG" ); throw e
                                                                                                                                                  }
                                                                                                                                              } )( v_52( v_0 ) )
                                                                                                                                          } )( v_52( mul( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) )( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) ) ) )
                                                                                                                                      } )( v_53( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) )
                                                                                                                                  } )( v_54( s( v_0 ) ) )
                                                                                                                              } )( v_55( v_0 ) )
                                                                                                                          } )( v_55( s( v_0 ) ) )
                                                                                                                      } )( v_56( s( v_0 ) ) )
                                                                                                                  } )( v_57( v_0 ) )
                                                                                                              } )( v_57( mul( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) )( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) ) )
                                                                                                          } )( v_57( s( v_0 ) ) )
                                                                                                      } )( v_58( mul( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) )( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) ) ) )
                                                                                                  } )( v_59( v_0 ) )
                                                                                              } )( v_60( mul( s( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) ) )( s( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) ) ) ) )
                                                                                          } )( v_61( s( mul( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) )( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) ) ) ) )
                                                                                      } )( v_62( mul( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) )( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) ) ) )
                                                                                  } )( v_63( v_0 ) )
                                                                              } )( v_64( mul( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) )( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) ) )
                                                                              println( s"ret = $ret" )
                                                                              ret
                                                                          } )
                                                                      } ) )( n )
                                                                  } ) )
                                                              } )( pi1[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_66 ) )
                                                          } )( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_66 ) )
                                                      } )( v_52( 0 ) )
                                                  } )( v_67( 0 ) )
                                              } )( v_57( 0 ) )
                                          } )( v_68( 0 ) )
                                      } )( v_69( s( 0 ) ) )
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
        //println( s"v_59: x=$x, y=$y" )
        if ( s( x ) == y ) {
          inl[Unit, Unit]( () )
        } else if ( s( x ) < y ) {
          inr[Unit, Unit]( () )
        } else {
          // Don't care
          inr[Unit, Unit]( () )
        }
      } )
    }
  }
  val arg10 = { x: Int =>
    { ( y: Int ) =>
      ( { _: Unit =>
        //println( s"v: x=$x, y=$y" )
        if ( x == y ) {
          inl[Unit, Unit]( () )
        } else if ( x < y ) {
          inr[Unit, Unit]( () )
        } else {
          // Don't care
          inr[Unit, Unit]( () )
        }
      }, { _: Sum[Unit, Unit] => () } )
    }
  }

  val realProg = prog( arg1 )( arg1 )( arg2 )( arg3 )( arg4 )( arg1 )( arg1 )( arg10 )

  List( 2 ) map ( i => println( s"floor(sqrt($i)) = ${realProg( i )._1}\n" ) )
  /*
  0 to 4 map ( i => println( s"floor(sqrt($i)) = ${realProg( i )._1}\n" ) )
  println( "Testing 1000 inputs" )
  0 to 1000 foreach ( i => {
    if ( Math.floor( Math.sqrt( i ) ).toInt != realProg( i )._1 ) {
      throw new Exception( s"realProg failed at input $i." )
    }
  } )
  */

}

object runtimeTypeError extends Script {

  val t: Tuple2[Int, Tuple2[Unit, Unit]] = ( 0, ( 1, ( (), () ) ) )

  def R[A]( b: A )( s: Int => A => A )( n: Int ): A = {
    if ( n == 0 ) {
      b
    } else {
      s( n )( R( b )( s )( n - 1 ) )
    }
  }
  def pi1[A, B]( p: ( A, B ) ): A = p._1
  def pi2[A, B]( p: ( A, B ) ): B = p._2
  def pair[A, B]( p0: A )( p1: B ): Tuple2[A, B] = {
    ( p0, p1 )
  }

  val base: Tuple2[Int, Tuple2[Unit, Unit]] = pair( 0 )( ( (), () ) )
  def step( n: Int )( prev: Tuple2[Int, Tuple2[Unit, Unit]] ): Tuple2[Int, Tuple2[Unit, Unit]] = {
    pair[Int, Tuple2[Unit, Unit]]( pi1( prev ) )( pair[Unit, Unit]( pi1( prev ) + 1 )( pi2( prev ) ) )
  }

  val ret = R( base )( step )( 2 )
  println( s"ret = $ret" )

  case class NewException[A]( m: A ) extends Exception

  def exception[A]( p: A ) = {
    new NewException( p )
  }

  val retTry: Tuple2[Unit, Unit] = try {
    ( { f: ( Tuple2[Int, Tuple2[Unit, Unit]] => Exception ) =>
      throw f( ( 1, ( (), () ) ) )
    } )( exception[Tuple2[Int, Tuple2[Unit, Unit]]] )
  } catch {
    case NewException( m: Tuple2[Unit, Unit] ) =>
      println( "case 2" )
      ( { x: Tuple2[Unit, Unit] => x } )( m )
    case NewException( m: Tuple2[Int, Tuple2[Unit, Unit]] ) =>
      println( "case 1" )
      ( { x: Tuple2[Unit, Unit] => x } )( m._2 )
  }
  println( s"retTry = $retTry" )

  /*
  val tmp1: Tuple2[Unit, Unit] = ( 1, ( (), () ) )
  println( tmp1 )
  val tmp: Tuple2[Unit, Unit] =
    try {
      throw NewException[Tuple2[Int, Tuple2[Unit, Unit]]]( ( 1, ( (), () ) ) )
    } catch {
      case NewException( m: Tuple2[Unit, Unit] ) =>
        println( s"matches Tuple2[Unit,Unit]: $m" ); m
      //case NewException( m: Tuple2[Int, Tuple2[Unit, Unit]] ) =>
      //println( s"matches Tuple2[Int, Tuple2[Unit,Unit]]: $m" ); m
    }
  */

  import shapeless._
  val `Tuple2[Unit,Unit]` = TypeCase[NewException[Tuple2[Unit, Unit]]]
  val `Tuple2[Int, Tuple2[Unit,Unit]]` = TypeCase[NewException[Tuple2[Int, Tuple2[Unit, Unit]]]]

  val tmpTypeable: Tuple2[Int, Tuple2[Unit, Unit]] =
    try {
      throw NewException[Tuple2[Unit, Unit]]( ( (), () ) )
    } catch {
      //case TypeCase[NewException[Tuple2[Int, Tuple2[Unit,Unit]]]]( e ) =>
      case `Tuple2[Int, Tuple2[Unit,Unit]]`( e ) =>
        println( s"matches Tuple2[Int, Tuple2[Unit,Unit]]: ${e.m}" ); e.m
    }
  println( s"tmp: ${tmpTypeable._2._1}" )

  case class PairUnitUnit( _1: Unit, _2: Unit )
  case class PairIntPairUnitUnit( _1: Int, _2: PairUnitUnit )
  val tmpPair: PairIntPairUnitUnit =
    try {
      throw NewException[PairUnitUnit]( PairUnitUnit( (), () ) )
    } catch {
      case NewException( m: PairIntPairUnitUnit ) =>
        println( s"matches Pair[Int, Pair[Unit,Unit]]: $m" ); m
    }
  println( s"tmpPair: ${tmpPair._2._1}" )

  val tmp: Tuple2[Int, Tuple2[Unit, Unit]] =
    try {
      throw NewException[Tuple2[Unit, Unit]]( ( (), () ) )
    } catch {
      case NewException( m: Tuple2[Int, Tuple2[Unit, Unit]] ) =>
        println( s"matches Tuple2[Int, Tuple2[Unit,Unit]]: $m" ); m
    }
  println( s"tmp: ${tmp._2._1}" )

  val tmp2: Unit = 1
  println( tmp2 )
  try {
    throw NewException( 1 )
  } catch {
    case NewException( m: Unit ) =>
      println( s"matches Unit: $m" )
    case NewException( m: Int ) =>
      println( s"matches Int: $m" )
  }

  /*
  val retTry: ( Unit, Unit ) = try {
    ( { f: ( ( Int, ( Unit, Unit ) ) => Exception ) =>
      throw f( ( 1, ( (), () ) ) )
    } )( exception[( Int, ( Unit, Unit ) )] )
  } catch {
    case NewException( m: ( Unit, Unit ) ) => m
  }
  */

}

object automaticProofWithTypeParamsKeepingGenericTypes extends Script {
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

  case class NewException[A]( m: A, id: Int ) extends Exception
  def exception[A]( m: A )( implicit id: Int = -1 ) = { new NewException( m, id ) }

  def pi1[A, B]( p: ( A, B ) ) = p._1

  def pair[A, B]( p0: A )( p1: B ): Tuple2[A, B] = ( p0, p1 )
  def efq[B]( p: Throwable ): B = { throw p }
  import shapeless._
  val `NewException[Tuple2[Int, Tuple2[Unit, Unit]]]` = TypeCase[NewException[Tuple2[Int, Tuple2[Unit, Unit]]]]
  val `NewException[Tuple2[Unit, Unit]]` = TypeCase[NewException[Tuple2[Unit, Unit]]]
  val `NewException[Unit]` = TypeCase[NewException[Unit]]
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
                                      ( {
                                        v_3: Unit =>
                                          ( {
                                            v_5: Unit =>
                                              ( {
                                                v_67: ( Int => Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] ) =>
                                                  ( {
                                                    v_66: Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] =>
                                                      ( {
                                                        v_4: Unit =>
                                                          ( {
                                                            v_7: ( Sum[Unit, Unit] => Unit ) =>
                                                              ( {
                                                                v_65: ( Unit => Sum[Unit, Unit] ) =>
                                                                  ( {
                                                                    v_1: ( Int => Tuple2[Int, Tuple2[Unit, Unit]] ) =>
                                                                      ( {
                                                                        v: Tuple2[Int, Tuple2[Unit, Unit]] => v
                                                                      } )( v_1( v_2 ) )
                                                                  } )( ( {
                                                                    n: Int =>
                                                                      natRec[Tuple2[Int, Tuple2[Unit, Unit]]]( pair[Int, Tuple2[Unit, Unit]]( 0 )( pair[Unit, Unit]( () )( ( {
                                                                        v_6: Unit => ()
                                                                      } )( v_7( inl[Unit, Unit]( () ) ) ) ) ) )( ( {
                                                                        v_0: Int =>
                                                                          ( {
                                                                            v_8: Tuple2[Int, Tuple2[Unit, Unit]] =>
                                                                              ( {
                                                                                v_63: ( Int => ( Unit => Unit ) ) =>
                                                                                  ( {
                                                                                    v_35: ( Unit => Unit ) =>
                                                                                      ( {
                                                                                        v_61: ( Int => ( Int => ( Tuple2[Unit, Unit] => Unit ) ) ) =>
                                                                                          ( {
                                                                                            v_60: ( Int => ( Tuple2[Unit, Unit] => Unit ) ) =>
                                                                                              ( {
                                                                                                v_20: ( Tuple2[Unit, Unit] => Unit ) =>
                                                                                                  ( {
                                                                                                    v_58: ( Int => ( Unit => Sum[Unit, Unit] ) ) =>
                                                                                                      ( {
                                                                                                        v_24: ( Unit => Sum[Unit, Unit] ) =>
                                                                                                          ( {
                                                                                                            v_54: ( Int => Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] ) =>
                                                                                                              ( {
                                                                                                                v_55: ( Int => Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] ) =>
                                                                                                                  ( {
                                                                                                                    v_56: ( Int => Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] ) =>
                                                                                                                      ( {
                                                                                                                        v_50: Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] =>
                                                                                                                          ( {
                                                                                                                            v_48: Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] =>
                                                                                                                              ( {
                                                                                                                                v_46: Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] =>
                                                                                                                                  ( {
                                                                                                                                    v_44: Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] =>
                                                                                                                                      ( {
                                                                                                                                        v_22: Unit =>
                                                                                                                                          ( {
                                                                                                                                            v_21: Unit =>
                                                                                                                                              ( {
                                                                                                                                                v_32: Unit =>
                                                                                                                                                  try {
                                                                                                                                                    ( {
                                                                                                                                                      v_11: ( Tuple2[Int, Tuple2[Unit, Unit]] => Exception ) =>
                                                                                                                                                        pair[Int, Tuple2[Unit, Unit]]( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) )(
                                                                                                                                                          try {
                                                                                                                                                            ( {
                                                                                                                                                              v_13: ( Tuple2[Unit, Unit] => Exception ) =>
                                                                                                                                                                efq[Tuple2[Unit, Unit]]( v_11( pair[Int, Tuple2[Unit, Unit]]( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) )( ( {
                                                                                                                                                                  v_38: Unit =>
                                                                                                                                                                    ( {
                                                                                                                                                                      v_25: Unit =>
                                                                                                                                                                        ( {
                                                                                                                                                                          v_31: ( Sum[Unit, Unit] => Unit ) =>
                                                                                                                                                                            ( {
                                                                                                                                                                              v_49: ( Unit => Sum[Unit, Unit] ) =>
                                                                                                                                                                                ( {
                                                                                                                                                                                  v_33: ( Sum[Unit, Unit] => Unit ) =>
                                                                                                                                                                                    ( {
                                                                                                                                                                                      v_47: ( Unit => Sum[Unit, Unit] ) =>
                                                                                                                                                                                        ( {
                                                                                                                                                                                          v_45: ( Sum[Unit, Unit] => Unit ) =>
                                                                                                                                                                                            ( {
                                                                                                                                                                                              v_37: ( Unit => Sum[Unit, Unit] ) =>
                                                                                                                                                                                                ( {
                                                                                                                                                                                                  v_42: ( Sum[Unit, Unit] => Unit ) =>
                                                                                                                                                                                                    ( {
                                                                                                                                                                                                      v_43: ( Unit => Sum[Unit, Unit] ) =>
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
                                                                                                                                                                                                                            efq[Tuple2[Unit, Unit]]( v_14( pair[Unit, Unit](
                                                                                                                                                                                                                              try {
                                                                                                                                                                                                                                ( {
                                                                                                                                                                                                                                  v_17: ( Unit => Exception ) =>
                                                                                                                                                                                                                                    efq[Unit]( v_13( pair[Unit, Unit]( ( {
                                                                                                                                                                                                                                      v_16: Sum[Unit, Unit] =>
                                                                                                                                                                                                                                        matchSum( v_16 )( ( {
                                                                                                                                                                                                                                          v_18: Unit =>
                                                                                                                                                                                                                                            efq[Unit]( v_17( ( {
                                                                                                                                                                                                                                              v_19: Unit =>
                                                                                                                                                                                                                                                ( {
                                                                                                                                                                                                                                                  v_15: Unit => v_15
                                                                                                                                                                                                                                                } )( () )
                                                                                                                                                                                                                                            } )( v_20( pair[Unit, Unit]( v_21 )( v_22 ) ) ) ) )
                                                                                                                                                                                                                                        } ) )( ( {
                                                                                                                                                                                                                                          v_23: Unit => v_23
                                                                                                                                                                                                                                        } ) )
                                                                                                                                                                                                                                    } )( v_24( v_25 ) ) )( ( {
                                                                                                                                                                                                                                      v_27: Sum[Unit, Unit] =>
                                                                                                                                                                                                                                        try {
                                                                                                                                                                                                                                          ( {
                                                                                                                                                                                                                                            v_28: ( Unit => Exception ) =>
                                                                                                                                                                                                                                              matchSum( v_27 )( ( {
                                                                                                                                                                                                                                                v_29: Unit =>
                                                                                                                                                                                                                                                  efq[Unit]( v_28( ( {
                                                                                                                                                                                                                                                    v_30: Unit => ()
                                                                                                                                                                                                                                                  } )( v_31( inr[Unit, Unit]( v_32 ) ) ) ) )
                                                                                                                                                                                                                                              } ) )( ( {
                                                                                                                                                                                                                                                v_36: Unit =>
                                                                                                                                                                                                                                                  ( {
                                                                                                                                                                                                                                                    v_26: Unit => v_26
                                                                                                                                                                                                                                                  } )( v_33( inr[Unit, Unit]( ( {
                                                                                                                                                                                                                                                    v_34: Unit => v_34
                                                                                                                                                                                                                                                  } )( v_35( v_36 ) ) ) ) )
                                                                                                                                                                                                                                              } ) )
                                                                                                                                                                                                                                          } )( exception[Unit]( _ )( 6 ) )
                                                                                                                                                                                                                                        } catch {
                                                                                                                                                                                                                                          case `NewException[Unit]`( e ) if e.id == 6 => {
                                                                                                                                                                                                                                            println( "thrown at " + e.id + " caught at 6" )
                                                                                                                                                                                                                                            ( {
                                                                                                                                                                                                                                              v_26: Unit => v_26
                                                                                                                                                                                                                                            } )( e.m )
                                                                                                                                                                                                                                          }
                                                                                                                                                                                                                                          case e => println( "BUG 6" ); throw e
                                                                                                                                                                                                                                        }
                                                                                                                                                                                                                                    } )( v_37( v_38 ) ) ) ) )
                                                                                                                                                                                                                                } )( exception[Unit]( _ )( 5 ) )
                                                                                                                                                                                                                              } catch {
                                                                                                                                                                                                                                case `NewException[Unit]`( e ) if e.id == 5 => {
                                                                                                                                                                                                                                  println( "thrown at " + e.id + " caught at 5" )
                                                                                                                                                                                                                                  ( {
                                                                                                                                                                                                                                    v_15: Unit => v_15
                                                                                                                                                                                                                                  } )( e.m )
                                                                                                                                                                                                                                }
                                                                                                                                                                                                                                case e => println( "BUG 5" ); throw e
                                                                                                                                                                                                                              } )(
                                                                                                                                                                                                                                try {
                                                                                                                                                                                                                                  ( {
                                                                                                                                                                                                                                    v_40: ( Unit => Exception ) =>
                                                                                                                                                                                                                                      efq[Unit]( v_13( pair[Unit, Unit]( ( {
                                                                                                                                                                                                                                        v_41: Unit =>
                                                                                                                                                                                                                                          ( {
                                                                                                                                                                                                                                            v_16: Sum[Unit, Unit] =>
                                                                                                                                                                                                                                              matchSum( v_16 )( ( {
                                                                                                                                                                                                                                                v_18: Unit => efq[Unit]( v_40( () ) )
                                                                                                                                                                                                                                              } ) )( ( {
                                                                                                                                                                                                                                                v_23: Unit => v_23
                                                                                                                                                                                                                                              } ) )
                                                                                                                                                                                                                                          } )( v_24( v_25 ) )
                                                                                                                                                                                                                                      } )( v_42( inl[Unit, Unit]( () ) ) ) )( ( {
                                                                                                                                                                                                                                        v_27: Sum[Unit, Unit] =>
                                                                                                                                                                                                                                          try {
                                                                                                                                                                                                                                            ( {
                                                                                                                                                                                                                                              v_28: ( Unit => Exception ) =>
                                                                                                                                                                                                                                                matchSum( v_27 )( ( {
                                                                                                                                                                                                                                                  v_29: Unit =>
                                                                                                                                                                                                                                                    efq[Unit]( v_28( ( {
                                                                                                                                                                                                                                                      v_30: Unit => ()
                                                                                                                                                                                                                                                    } )( v_31( inr[Unit, Unit]( v_32 ) ) ) ) )
                                                                                                                                                                                                                                                } ) )( ( {
                                                                                                                                                                                                                                                  v_36: Unit =>
                                                                                                                                                                                                                                                    ( {
                                                                                                                                                                                                                                                      v_26: Unit => v_26
                                                                                                                                                                                                                                                    } )( v_33( inr[Unit, Unit]( ( {
                                                                                                                                                                                                                                                      v_34: Unit => v_34
                                                                                                                                                                                                                                                    } )( v_35( v_36 ) ) ) ) )
                                                                                                                                                                                                                                                } ) )
                                                                                                                                                                                                                                            } )( exception[Unit]( _ )( 8 ) )
                                                                                                                                                                                                                                          } catch {
                                                                                                                                                                                                                                            case `NewException[Unit]`( e ) if e.id == 8 => {
                                                                                                                                                                                                                                              println( "thrown at " + e.id + " caught at 8" )
                                                                                                                                                                                                                                              ( {
                                                                                                                                                                                                                                                v_26: Unit => v_26
                                                                                                                                                                                                                                              } )( e.m )
                                                                                                                                                                                                                                            }
                                                                                                                                                                                                                                            case e => println( "BUG 8" ); throw e
                                                                                                                                                                                                                                          }
                                                                                                                                                                                                                                      } )( v_37( v_38 ) ) ) ) )
                                                                                                                                                                                                                                  } )( exception[Unit]( _ )( 7 ) )
                                                                                                                                                                                                                                } catch {
                                                                                                                                                                                                                                  case `NewException[Unit]`( e ) if e.id == 7 => {
                                                                                                                                                                                                                                    println( "thrown at " + e.id + " caught at 7" )
                                                                                                                                                                                                                                    ( {
                                                                                                                                                                                                                                      v_39: Unit => v_39
                                                                                                                                                                                                                                    } )( e.m )
                                                                                                                                                                                                                                  }
                                                                                                                                                                                                                                  case e => println( "BUG 7" ); throw e
                                                                                                                                                                                                                                } ) ) )
                                                                                                                                                                                                                        } )( exception[Tuple2[Unit, Unit]]( _ )( 4 ) )
                                                                                                                                                                                                                      } catch {
                                                                                                                                                                                                                        case `NewException[Tuple2[Unit, Unit]]`( e ) if e.id == 4 => {
                                                                                                                                                                                                                          println( "thrown at " + e.id + " caught at 4" )
                                                                                                                                                                                                                          ( {
                                                                                                                                                                                                                            v_10: Tuple2[Unit, Unit] => v_10
                                                                                                                                                                                                                          } )( e.m )
                                                                                                                                                                                                                        }
                                                                                                                                                                                                                        case e => println( "BUG 4" ); throw e
                                                                                                                                                                                                                      }
                                                                                                                                                                                                                  } )( exception[Tuple2[Unit, Unit]]( _ )( 3 ) )
                                                                                                                                                                                                                } catch {
                                                                                                                                                                                                                  case `NewException[Tuple2[Unit, Unit]]`( e ) if e.id == 3 => {
                                                                                                                                                                                                                    println( "thrown at " + e.id + " caught at 3" )
                                                                                                                                                                                                                    ( {
                                                                                                                                                                                                                      v_10: Tuple2[Unit, Unit] => v_10
                                                                                                                                                                                                                    } )( e.m )
                                                                                                                                                                                                                  }
                                                                                                                                                                                                                  case e => println( "BUG 3" ); throw e
                                                                                                                                                                                                                } ) )
                                                                                                                                                                                                          } )( exception[Tuple2[Unit, Unit]]( _ )( 2 ) )
                                                                                                                                                                                                        } catch {
                                                                                                                                                                                                          case `NewException[Tuple2[Unit, Unit]]`( e ) if e.id == 2 => {
                                                                                                                                                                                                            println( "thrown at " + e.id + " caught at 2" )
                                                                                                                                                                                                            ( {
                                                                                                                                                                                                              v_12: Tuple2[Unit, Unit] => v_12
                                                                                                                                                                                                            } )( e.m )
                                                                                                                                                                                                          }
                                                                                                                                                                                                          case e => println( "BUG 2" ); throw e
                                                                                                                                                                                                        }
                                                                                                                                                                                                    } )( pi1[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_44 ) )
                                                                                                                                                                                                } )( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_44 ) )
                                                                                                                                                                                            } )( pi1[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_46 ) )
                                                                                                                                                                                        } )( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_46 ) )
                                                                                                                                                                                    } )( pi1[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_48 ) )
                                                                                                                                                                                } )( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_48 ) )
                                                                                                                                                                            } )( pi1[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_50 ) )
                                                                                                                                                                        } )( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_50 ) )
                                                                                                                                                                    } )( pi1[Unit, Unit]( pi2[Int, Tuple2[Unit, Unit]]( v_8 ) ) )
                                                                                                                                                                } )( pi2[Unit, Unit]( pi2[Int, Tuple2[Unit, Unit]]( v_8 ) ) ) ) ) )
                                                                                                                                                            } )( exception[Tuple2[Unit, Unit]]( _ )( 1 ) )
                                                                                                                                                          } catch {
                                                                                                                                                            case `NewException[Tuple2[Unit, Unit]]`( e ) if e.id == 1 => {
                                                                                                                                                              println( "thrown at " + e.id + " caught at 1" )
                                                                                                                                                              ( {
                                                                                                                                                                v_10: Tuple2[Unit, Unit] => v_10
                                                                                                                                                              } )( e.m )
                                                                                                                                                            }
                                                                                                                                                            case e => println( "BUG 1" ); throw e
                                                                                                                                                          } )
                                                                                                                                                    } )( exception[Tuple2[Int, Tuple2[Unit, Unit]]]( _ )( 0 ) )
                                                                                                                                                  } catch {
                                                                                                                                                    case `NewException[Tuple2[Int, Tuple2[Unit, Unit]]]`( e ) if e.id == 0 => {
                                                                                                                                                      println( "thrown at " + e.id + " caught at 0" )
                                                                                                                                                      ( {
                                                                                                                                                        v_9: Tuple2[Int, Tuple2[Unit, Unit]] => v_9
                                                                                                                                                      } )( e.m )
                                                                                                                                                    }
                                                                                                                                                    case e => println( "BUG 0" ); throw e
                                                                                                                                                  }
                                                                                                                                              } )( v_52( v_0 ) )
                                                                                                                                          } )( v_52( mul( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) )( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) ) ) )
                                                                                                                                      } )( v_53( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) )
                                                                                                                                  } )( v_54( s( v_0 ) ) )
                                                                                                                              } )( v_55( v_0 ) )
                                                                                                                          } )( v_55( s( v_0 ) ) )
                                                                                                                      } )( v_56( s( v_0 ) ) )
                                                                                                                  } )( v_57( v_0 ) )
                                                                                                              } )( v_57( mul( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) )( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) ) )
                                                                                                          } )( v_57( s( v_0 ) ) )
                                                                                                      } )( v_58( mul( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) )( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) ) ) )
                                                                                                  } )( v_59( v_0 ) )
                                                                                              } )( v_60( mul( s( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) ) )( s( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) ) ) ) )
                                                                                          } )( v_61( s( mul( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) )( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) ) ) ) )
                                                                                      } )( v_62( mul( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) )( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) ) ) )
                                                                                  } )( v_63( v_0 ) )
                                                                              } )( v_64( mul( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) )( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) ) )
                                                                          } )
                                                                      } ) )( n )
                                                                  } ) )
                                                              } )( pi1[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_66 ) )
                                                          } )( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_66 ) )
                                                      } )( v_52( 0 ) )
                                                  } )( v_67( 0 ) )
                                              } )( v_57( 0 ) )
                                          } )( v_68( 0 ) )
                                      } )( v_69( s( 0 ) ) )
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
        //println( s"v_59: x=$x, y=$y" )
        if ( s( x ) == y ) {
          inl[Unit, Unit]( () )
        } else if ( s( x ) < y ) {
          inr[Unit, Unit]( () )
        } else {
          // Don't care
          inr[Unit, Unit]( () )
        }
      } )
    }
  }
  val arg10 = { x: Int =>
    { ( y: Int ) =>
      ( { _: Unit =>
        //println( s"v: x=$x, y=$y" )
        if ( x == y ) {
          inl[Unit, Unit]( () )
        } else if ( x < y ) {
          inr[Unit, Unit]( () )
        } else {
          // Don't care
          inr[Unit, Unit]( () )
        }
      }, { _: Sum[Unit, Unit] => () } )
    }
  }

  val realProg = prog( arg1 )( arg1 )( arg2 )( arg3 )( arg4 )( arg1 )( arg1 )( arg10 )

  0 to 4 map ( i => println( s"floor(sqrt($i)) = ${realProg( i )._1}\n" ) )
  println( "Testing 1000 inputs" )
  0 to 1000 foreach ( i => {
    if ( Math.floor( Math.sqrt( i ) ).toInt != realProg( i )._1 ) {
      throw new Exception( s"realProg failed at input $i." )
    }
  } )

}

object simplerProof extends Script {
  def s( x: Int ) = x + 1
  def mul( x: Int )( y: Int ) = x * y
  def leq( x: Int )( y: Int ) = x <= y

  def pow2( x: Int ) = x * x
  def pi2[A, B]( p: ( A, B ) ) = p._2
  sealed trait Sum[A, B]
  final case class Inr[A, B]( v: B ) extends Sum[A, B]

  def matchSum[A, B, C]( p1: Sum[A, B] )( p2: A => C )( p3: B => C ) = {
    p1 match {
      case Inl( a ) => p2( a )
      case Inr( b ) => p3( b )
    }
  }

  def eq[X]( x: X )( y: X ) = x == y
  def lt( x: Int )( y: Int ) = x < y
  final case class Inl[A, B]( v: A ) extends Sum[A, B]

  def natRec[A]( p1: A )( p2: ( Int => A => A ) )( p3: Int ): A = {
    if ( p3 == 0 ) {
      p1
    } else {
      p2( p3 - 1 )( natRec( p1 )( p2 )( p3 - 1 ) )
    }
  }

  case class Exn[A]( v: A, id: Option[Int] ) extends Exception
  def exception[A]( v: A )( id: Option[Int] = None ) = new Exn( v, id )

  def pi1[A, B]( p: ( A, B ) ) = p._1

  def pair[A, B]( p0: A )( p1: B ): Tuple2[A, B] = ( p0, p1 )
  def efq[B]( p: Throwable ): B = throw p
  import shapeless._
  val `Exn[Tuple2[Int, Tuple2[Unit, Unit]]]` = TypeCase[Exn[Tuple2[Int, Tuple2[Unit, Unit]]]]
  val `Exn[Tuple2[Unit, Unit]]` = TypeCase[Exn[Tuple2[Unit, Unit]]]
  val `Exn[Unit]` = TypeCase[Exn[Unit]]
  val prog = ( {
    v_68: ( Int => Unit ) =>
      ( {
        v_67: ( Int => Unit ) =>
          ( {
            v_58: ( Int => ( Int => ( Unit => Sum[Unit, Unit] ) ) ) =>
              ( {
                v_52: ( Int => Unit ) =>
                  ( {
                    v_63: ( Int => ( Int => ( Int => ( Tuple2[Unit, Unit] => Unit ) ) ) ) =>
                      ( {
                        v_51: ( Int => Unit ) =>
                          ( {
                            v_56: ( Int => ( Int => Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] ) ) =>
                              ( {
                                v_2: Int =>
                                  ( {
                                    v_3: Unit =>
                                      ( {
                                        v_5: Unit =>
                                          ( {
                                            v_66: ( Int => Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] ) =>
                                              ( {
                                                v_65: Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] =>
                                                  ( {
                                                    v_4: Unit =>
                                                      ( {
                                                        v_7: ( Sum[Unit, Unit] => Unit ) =>
                                                          ( {
                                                            v_64: ( Unit => Sum[Unit, Unit] ) =>
                                                              ( {
                                                                v_1: ( Int => Tuple2[Int, Tuple2[Unit, Unit]] ) =>
                                                                  ( {
                                                                    v: Tuple2[Int, Tuple2[Unit, Unit]] => v
                                                                  } )( v_1( v_2 ) )
                                                              } )( ( {
                                                                n: Int =>
                                                                  natRec[Tuple2[Int, Tuple2[Unit, Unit]]]( pair[Int, Tuple2[Unit, Unit]]( 0 )( pair[Unit, Unit]( () )( ( {
                                                                    v_6: Unit => ()
                                                                  } )( v_7( Inl[Unit, Unit]( () ) ) ) ) ) )( ( {
                                                                    v_0: Int =>
                                                                      ( {
                                                                        v_8: Tuple2[Int, Tuple2[Unit, Unit]] =>
                                                                          ( {
                                                                            v_60: ( Int => ( Int => ( Tuple2[Unit, Unit] => Unit ) ) ) =>
                                                                              ( {
                                                                                v_62: ( Int => ( Int => ( Tuple2[Unit, Unit] => Unit ) ) ) =>
                                                                                  ( {
                                                                                    v_61: ( Int => ( Tuple2[Unit, Unit] => Unit ) ) =>
                                                                                      ( {
                                                                                        v_34: ( Tuple2[Unit, Unit] => Unit ) =>
                                                                                          ( {
                                                                                            v_59: ( Int => ( Tuple2[Unit, Unit] => Unit ) ) =>
                                                                                              ( {
                                                                                                v_18: ( Tuple2[Unit, Unit] => Unit ) =>
                                                                                                  ( {
                                                                                                    v_57: ( Int => ( Unit => Sum[Unit, Unit] ) ) =>
                                                                                                      ( {
                                                                                                        v_23: ( Unit => Sum[Unit, Unit] ) =>
                                                                                                          ( {
                                                                                                            v_53: ( Int => Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] ) =>
                                                                                                              ( {
                                                                                                                v_54: ( Int => Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] ) =>
                                                                                                                  ( {
                                                                                                                    v_55: ( Int => Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] ) =>
                                                                                                                      ( {
                                                                                                                        v_49: Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] =>
                                                                                                                          ( {
                                                                                                                            v_47: Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] =>
                                                                                                                              ( {
                                                                                                                                v_45: Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] =>
                                                                                                                                  ( {
                                                                                                                                    v_43: Tuple2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )] =>
                                                                                                                                      ( {
                                                                                                                                        v_21: Unit =>
                                                                                                                                          ( {
                                                                                                                                            v_20: Unit =>
                                                                                                                                              ( {
                                                                                                                                                v_31: Unit =>
                                                                                                                                                  try {
                                                                                                                                                    ( {
                                                                                                                                                      v_11: ( Tuple2[Int, Tuple2[Unit, Unit]] => Exception ) =>
                                                                                                                                                        pair[Int, Tuple2[Unit, Unit]]( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) )(
                                                                                                                                                          try {
                                                                                                                                                            ( {
                                                                                                                                                              v_13: ( Tuple2[Unit, Unit] => Exception ) =>
                                                                                                                                                                efq[Tuple2[Unit, Unit]]( v_11( pair[Int, Tuple2[Unit, Unit]]( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) )( ( {
                                                                                                                                                                  v_37: Unit =>
                                                                                                                                                                    ( {
                                                                                                                                                                      v_24: Unit =>
                                                                                                                                                                        ( {
                                                                                                                                                                          v_30: ( Sum[Unit, Unit] => Unit ) =>
                                                                                                                                                                            ( {
                                                                                                                                                                              v_48: ( Unit => Sum[Unit, Unit] ) =>
                                                                                                                                                                                ( {
                                                                                                                                                                                  v_32: ( Sum[Unit, Unit] => Unit ) =>
                                                                                                                                                                                    ( {
                                                                                                                                                                                      v_46: ( Unit => Sum[Unit, Unit] ) =>
                                                                                                                                                                                        ( {
                                                                                                                                                                                          v_44: ( Sum[Unit, Unit] => Unit ) =>
                                                                                                                                                                                            ( {
                                                                                                                                                                                              v_36: ( Unit => Sum[Unit, Unit] ) =>
                                                                                                                                                                                                ( {
                                                                                                                                                                                                  v_41: ( Sum[Unit, Unit] => Unit ) =>
                                                                                                                                                                                                    ( {
                                                                                                                                                                                                      v_42: ( Unit => Sum[Unit, Unit] ) =>
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
                                                                                                                                                                                                                            efq[Tuple2[Unit, Unit]]( v_14( pair[Unit, Unit](
                                                                                                                                                                                                                              try {
                                                                                                                                                                                                                                ( {
                                                                                                                                                                                                                                  v_17: ( Unit => Exception ) =>
                                                                                                                                                                                                                                    efq[Unit]( v_13( pair[Unit, Unit]( ( {
                                                                                                                                                                                                                                      v_16: Sum[Unit, Unit] =>
                                                                                                                                                                                                                                        matchSum( v_16 )( ( {
                                                                                                                                                                                                                                          v_19: Unit =>
                                                                                                                                                                                                                                            efq[Unit]( v_17( ( {
                                                                                                                                                                                                                                              v_15: Unit => v_15
                                                                                                                                                                                                                                            } )( v_18( pair[Unit, Unit]( () )( v_21 ) ) ) ) )
                                                                                                                                                                                                                                        } ) )( ( {
                                                                                                                                                                                                                                          v_22: Unit => v_22
                                                                                                                                                                                                                                        } ) )
                                                                                                                                                                                                                                    } )( v_23( v_24 ) ) )( ( {
                                                                                                                                                                                                                                      v_26: Sum[Unit, Unit] =>
                                                                                                                                                                                                                                        try {
                                                                                                                                                                                                                                          ( {
                                                                                                                                                                                                                                            v_27: ( Unit => Exception ) =>
                                                                                                                                                                                                                                              matchSum( v_26 )( ( {
                                                                                                                                                                                                                                                v_28: Unit =>
                                                                                                                                                                                                                                                  efq[Unit]( v_27( ( {
                                                                                                                                                                                                                                                    v_29: Unit => ()
                                                                                                                                                                                                                                                  } )( v_30( Inr[Unit, Unit]( v_31 ) ) ) ) )
                                                                                                                                                                                                                                              } ) )( ( {
                                                                                                                                                                                                                                                v_35: Unit =>
                                                                                                                                                                                                                                                  ( {
                                                                                                                                                                                                                                                    v_25: Unit => v_25
                                                                                                                                                                                                                                                  } )( v_32( Inr[Unit, Unit]( ( {
                                                                                                                                                                                                                                                    v_33: Unit => v_33
                                                                                                                                                                                                                                                  } )( v_34( pair[Unit, Unit]( v_35 )( v_31 ) ) ) ) ) )
                                                                                                                                                                                                                                              } ) )
                                                                                                                                                                                                                                          } )( exception[Unit]( _ )( Some( 6 ) ) )
                                                                                                                                                                                                                                        } catch {
                                                                                                                                                                                                                                          case `Exn[Unit]`( e ) if e.id == Some( 6 ) => {
                                                                                                                                                                                                                                            //println( "thrown at " + e.id + " caught at 6" )
                                                                                                                                                                                                                                            ( {
                                                                                                                                                                                                                                              v_25: Unit => v_25
                                                                                                                                                                                                                                            } )( e.v )
                                                                                                                                                                                                                                          }
                                                                                                                                                                                                                                          case e => {
                                                                                                                                                                                                                                            //println("throwing further at 6")
                                                                                                                                                                                                                                            throw e
                                                                                                                                                                                                                                          }
                                                                                                                                                                                                                                        }
                                                                                                                                                                                                                                    } )( v_36( v_37 ) ) ) ) )
                                                                                                                                                                                                                                } )( exception[Unit]( _ )( Some( 5 ) ) )
                                                                                                                                                                                                                              } catch {
                                                                                                                                                                                                                                case `Exn[Unit]`( e ) if e.id == Some( 5 ) => {
                                                                                                                                                                                                                                  //println( "thrown at " + e.id + " caught at 5" )
                                                                                                                                                                                                                                  ( {
                                                                                                                                                                                                                                    v_15: Unit => v_15
                                                                                                                                                                                                                                  } )( e.v )
                                                                                                                                                                                                                                }
                                                                                                                                                                                                                                case e => {
                                                                                                                                                                                                                                  //println("throwing further at 5")
                                                                                                                                                                                                                                  throw e
                                                                                                                                                                                                                                }
                                                                                                                                                                                                                              } )(
                                                                                                                                                                                                                                try {
                                                                                                                                                                                                                                  ( {
                                                                                                                                                                                                                                    v_39: ( Unit => Exception ) =>
                                                                                                                                                                                                                                      efq[Unit]( v_13( pair[Unit, Unit]( ( {
                                                                                                                                                                                                                                        v_40: Unit =>
                                                                                                                                                                                                                                          ( {
                                                                                                                                                                                                                                            v_16: Sum[Unit, Unit] =>
                                                                                                                                                                                                                                              matchSum( v_16 )( ( {
                                                                                                                                                                                                                                                v_19: Unit => efq[Unit]( v_39( () ) )
                                                                                                                                                                                                                                              } ) )( ( {
                                                                                                                                                                                                                                                v_22: Unit => v_22
                                                                                                                                                                                                                                              } ) )
                                                                                                                                                                                                                                          } )( v_23( v_24 ) )
                                                                                                                                                                                                                                      } )( v_41( Inl[Unit, Unit]( () ) ) ) )( ( {
                                                                                                                                                                                                                                        v_26: Sum[Unit, Unit] =>
                                                                                                                                                                                                                                          try {
                                                                                                                                                                                                                                            ( {
                                                                                                                                                                                                                                              v_27: ( Unit => Exception ) =>
                                                                                                                                                                                                                                                matchSum( v_26 )( ( {
                                                                                                                                                                                                                                                  v_28: Unit =>
                                                                                                                                                                                                                                                    efq[Unit]( v_27( ( {
                                                                                                                                                                                                                                                      v_29: Unit => ()
                                                                                                                                                                                                                                                    } )( v_30( Inr[Unit, Unit]( v_31 ) ) ) ) )
                                                                                                                                                                                                                                                } ) )( ( {
                                                                                                                                                                                                                                                  v_35: Unit =>
                                                                                                                                                                                                                                                    ( {
                                                                                                                                                                                                                                                      v_25: Unit => v_25
                                                                                                                                                                                                                                                    } )( v_32( Inr[Unit, Unit]( ( {
                                                                                                                                                                                                                                                      v_33: Unit => v_33
                                                                                                                                                                                                                                                    } )( v_34( pair[Unit, Unit]( v_35 )( v_31 ) ) ) ) ) )
                                                                                                                                                                                                                                                } ) )
                                                                                                                                                                                                                                            } )( exception[Unit]( _ )( Some( 8 ) ) )
                                                                                                                                                                                                                                          } catch {
                                                                                                                                                                                                                                            case `Exn[Unit]`( e ) if e.id == Some( 8 ) => {
                                                                                                                                                                                                                                              //println( "thrown at " + e.id + " caught at 8" )
                                                                                                                                                                                                                                              ( {
                                                                                                                                                                                                                                                v_25: Unit => v_25
                                                                                                                                                                                                                                              } )( e.v )
                                                                                                                                                                                                                                            }
                                                                                                                                                                                                                                            case e => {
                                                                                                                                                                                                                                              //println("throwing further at 8")
                                                                                                                                                                                                                                              throw e
                                                                                                                                                                                                                                            }
                                                                                                                                                                                                                                          }
                                                                                                                                                                                                                                      } )( v_36( v_37 ) ) ) ) )
                                                                                                                                                                                                                                  } )( exception[Unit]( _ )( Some( 7 ) ) )
                                                                                                                                                                                                                                } catch {
                                                                                                                                                                                                                                  case `Exn[Unit]`( e ) if e.id == Some( 7 ) => {
                                                                                                                                                                                                                                    //println( "thrown at " + e.id + " caught at 7" )
                                                                                                                                                                                                                                    ( {
                                                                                                                                                                                                                                      v_38: Unit => v_38
                                                                                                                                                                                                                                    } )( e.v )
                                                                                                                                                                                                                                  }
                                                                                                                                                                                                                                  case e => {
                                                                                                                                                                                                                                    //println("throwing further at 7")
                                                                                                                                                                                                                                    throw e
                                                                                                                                                                                                                                  }
                                                                                                                                                                                                                                } ) ) )
                                                                                                                                                                                                                        } )( exception[Tuple2[Unit, Unit]]( _ )( Some( 4 ) ) )
                                                                                                                                                                                                                      } catch {
                                                                                                                                                                                                                        case `Exn[Tuple2[Unit, Unit]]`( e ) if e.id == Some( 4 ) => {
                                                                                                                                                                                                                          //println( "thrown at " + e.id + " caught at 4" )
                                                                                                                                                                                                                          ( {
                                                                                                                                                                                                                            v_10: Tuple2[Unit, Unit] => v_10
                                                                                                                                                                                                                          } )( e.v )
                                                                                                                                                                                                                        }
                                                                                                                                                                                                                        case e => {
                                                                                                                                                                                                                          //println("throwing further at 4")
                                                                                                                                                                                                                          throw e
                                                                                                                                                                                                                        }
                                                                                                                                                                                                                      }
                                                                                                                                                                                                                  } )( exception[Tuple2[Unit, Unit]]( _ )( Some( 3 ) ) )
                                                                                                                                                                                                                } catch {
                                                                                                                                                                                                                  case `Exn[Tuple2[Unit, Unit]]`( e ) if e.id == Some( 3 ) => {
                                                                                                                                                                                                                    //println( "thrown at " + e.id + " caught at 3" )
                                                                                                                                                                                                                    ( {
                                                                                                                                                                                                                      v_10: Tuple2[Unit, Unit] => v_10
                                                                                                                                                                                                                    } )( e.v )
                                                                                                                                                                                                                  }
                                                                                                                                                                                                                  case e => {
                                                                                                                                                                                                                    //println("throwing further at 3")
                                                                                                                                                                                                                    throw e
                                                                                                                                                                                                                  }
                                                                                                                                                                                                                } ) )
                                                                                                                                                                                                          } )( exception[Tuple2[Unit, Unit]]( _ )( Some( 2 ) ) )
                                                                                                                                                                                                        } catch {
                                                                                                                                                                                                          case `Exn[Tuple2[Unit, Unit]]`( e ) if e.id == Some( 2 ) => {
                                                                                                                                                                                                            //println( "thrown at " + e.id + " caught at 2" )
                                                                                                                                                                                                            ( {
                                                                                                                                                                                                              v_12: Tuple2[Unit, Unit] => v_12
                                                                                                                                                                                                            } )( e.v )
                                                                                                                                                                                                          }
                                                                                                                                                                                                          case e => {
                                                                                                                                                                                                            //println("throwing further at 2")
                                                                                                                                                                                                            throw e
                                                                                                                                                                                                          }
                                                                                                                                                                                                        }
                                                                                                                                                                                                    } )( pi1[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_43 ) )
                                                                                                                                                                                                } )( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_43 ) )
                                                                                                                                                                                            } )( pi1[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_45 ) )
                                                                                                                                                                                        } )( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_45 ) )
                                                                                                                                                                                    } )( pi1[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_47 ) )
                                                                                                                                                                                } )( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_47 ) )
                                                                                                                                                                            } )( pi1[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_49 ) )
                                                                                                                                                                        } )( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_49 ) )
                                                                                                                                                                    } )( pi1[Unit, Unit]( pi2[Int, Tuple2[Unit, Unit]]( v_8 ) ) )
                                                                                                                                                                } )( pi2[Unit, Unit]( pi2[Int, Tuple2[Unit, Unit]]( v_8 ) ) ) ) ) )
                                                                                                                                                            } )( exception[Tuple2[Unit, Unit]]( _ )( Some( 1 ) ) )
                                                                                                                                                          } catch {
                                                                                                                                                            case `Exn[Tuple2[Unit, Unit]]`( e ) if e.id == Some( 1 ) => {
                                                                                                                                                              //println( "thrown at " + e.id + " caught at 1" )
                                                                                                                                                              ( {
                                                                                                                                                                v_10: Tuple2[Unit, Unit] => v_10
                                                                                                                                                              } )( e.v )
                                                                                                                                                            }
                                                                                                                                                            case e => {
                                                                                                                                                              //println("throwing further at 1")
                                                                                                                                                              throw e
                                                                                                                                                            }
                                                                                                                                                          } )
                                                                                                                                                    } )( exception[Tuple2[Int, Tuple2[Unit, Unit]]]( _ )( Some( 0 ) ) )
                                                                                                                                                  } catch {
                                                                                                                                                    case `Exn[Tuple2[Int, Tuple2[Unit, Unit]]]`( e ) if e.id == Some( 0 ) => {
                                                                                                                                                      //println( "thrown at " + e.id + " caught at 0" )
                                                                                                                                                      ( {
                                                                                                                                                        v_9: Tuple2[Int, Tuple2[Unit, Unit]] => v_9
                                                                                                                                                      } )( e.v )
                                                                                                                                                    }
                                                                                                                                                    case e => {
                                                                                                                                                      //println("throwing further at 0")
                                                                                                                                                      throw e
                                                                                                                                                    }
                                                                                                                                                  }
                                                                                                                                              } )( v_51( v_0 ) )
                                                                                                                                          } )( v_51( s( v_0 ) ) )
                                                                                                                                      } )( v_52( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) )
                                                                                                                                  } )( v_53( s( v_0 ) ) )
                                                                                                                              } )( v_54( v_0 ) )
                                                                                                                          } )( v_54( s( v_0 ) ) )
                                                                                                                      } )( v_55( s( v_0 ) ) )
                                                                                                                  } )( v_56( v_0 ) )
                                                                                                              } )( v_56( mul( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) )( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) ) )
                                                                                                          } )( v_56( s( v_0 ) ) )
                                                                                                      } )( v_57( mul( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) )( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) ) ) )
                                                                                                  } )( v_58( v_0 ) )
                                                                                              } )( v_59( mul( s( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) ) )( s( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) ) ) ) )
                                                                                          } )( v_60( s( mul( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) )( s( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) ) ) ) )
                                                                                      } )( v_61( s( v_0 ) ) )
                                                                                  } )( v_62( v_0 ) )
                                                                              } )( v_63( mul( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) )( pi1[Int, Tuple2[Unit, Unit]]( v_8 ) ) ) )
                                                                          } )( v_63( s( v_0 ) ) )
                                                                      } )
                                                                  } ) )( n )
                                                              } ) )
                                                          } )( pi1[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_65 ) )
                                                      } )( pi2[( Unit => Sum[Unit, Unit] ), ( Sum[Unit, Unit] => Unit )]( v_65 ) )
                                                  } )( v_51( 0 ) )
                                              } )( v_66( 0 ) )
                                          } )( v_56( 0 ) )
                                      } )( v_67( 0 ) )
                                  } )( v_68( s( 0 ) ) )
                              } )
                          } )
                      } )
                  } )
              } )
          } )
      } )
  } )

  val arg1 = { _: Int => () }
  val arg3 = { _: Int => { _: Int => { _: Int => { _: Tuple2[Unit, Unit] => () } } } }
  val arg4 = { x: Int =>
    { y: Int =>
      { _: Unit =>
        //println( s"v_59: x=$x, y=$y" )
        if ( s( x ) == y ) {
          Inl[Unit, Unit]( () )
        } else if ( s( x ) < y ) {
          Inr[Unit, Unit]( () )
        } else {
          // Don't care
          Inr[Unit, Unit]( () )
        }
      }
    }
  }
  val arg10 = { x: Int =>
    { ( y: Int ) =>
      ( { _: Unit =>
        //println( s"v: x=$x, y=$y" )
        if ( x == y ) {
          Inl[Unit, Unit]( () )
        } else if ( x < y ) {
          Inr[Unit, Unit]( () )
        } else {
          // Don't care
          Inr[Unit, Unit]( () )
        }
      }, { _: Sum[Unit, Unit] => () } )
    }
  }

  val realProg = prog( arg1 )( arg1 )( arg4 )( arg1 )( arg3 )( arg1 )( arg10 )

  0 to 4 foreach ( i => println( s"floor(sqrt($i)) = ${realProg( i )._1}\n" ) )
  println( "Testing 1000 inputs" )
  0 to 1000 foreach ( i => {
    if ( Math.floor( Math.sqrt( i ) ).toInt != realProg( i )._1 ) {
      throw new Exception( s"realProg failed at input $i." )
    }
  } )
}
