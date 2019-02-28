package gapt.examples

import extraction.{ FSharpCodeGenerator, ScalaCodeGenerator }
import gapt.examples.theories.nat
import gapt.proofs.nd._
import gapt.expr.{ TBase, _ }
import gapt.formats.babel.{ Notation, Precedence }
import gapt.formats.json.JsonImporter
import gapt.proofs
import gapt.proofs.context.Context
import gapt.proofs.{ Ant, Checkable, ProofBuilder, Sequent, Suc }
import gapt.proofs.context.update.{ InductiveType, PrimitiveRecursiveFunction, ReductionRuleUpdate }
import gapt.proofs.lk.rules._
import gapt.proofs.lk.transformations.{ LKToND, eliminateDefinitions }
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
    //println( FSharpCodeGenerator.apply( m1 )( ClassicalExtraction.systemT( ctx ) ) )
    println( ScalaCodeGenerator( m1 )( ClassicalExtraction.systemT( ctx ) ) )
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
  val s1 = gapt.proofs.lk.rules.LogicalAxiom( hof"A" )
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
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
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

object sqrtProofManualCorrectAxiomClassical extends Script {

  import gapt.expr._
  import gapt.formats.babel.{ Notation, Precedence }
  import gapt.proofs.context.Context
  import gapt.proofs.nd._

  implicit var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
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

object sqrtProofManualCorrectAxiomClassicalDifferentEMFormulasUsingEFQ extends Script {

  import gapt.expr._
  import gapt.formats.babel.{ Notation, Precedence }
  import gapt.proofs.context.Context
  import gapt.proofs.nd._

  implicit var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
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

object sqrtSimplerProof extends Script {
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

object tapeProofAutomatic extends Script {
  def s( x: Int ) = x + 1

  def leq( x: Int )( y: Int ) = x <= y

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

  case class Exn[A]( v: A, id: Option[Int] ) extends Exception

  def exception[A]( v: A )( id: Option[Int] = None ) = new Exn( v, id )

  def pi1[A, B]( p: ( A, B ) ) = p._1

  def pair[A, B]( p0: A )( p1: B ): Tuple2[A, B] = ( p0, p1 )

  def efq[B]( p: Throwable ): B = throw p

  def max( a: Int )( b: Int ): Int = if ( a >= b ) a else b

  ( {
    vLambda_45: ( Int => Sum[Unit, Unit] ) =>
      ( {
        vLambda_41: ( Int => ( Int => Unit ) ) =>
          ( {
            vLambda_36: ( Int => ( Int => Unit ) ) =>
              ( {
                vLambda_6: ( Int => ( Int => ( Unit => Unit ) ) ) =>
                  ( {
                    vLambda_13: ( Int => ( Int => ( Int => ( Tuple2[Unit, Unit] => Unit ) ) ) ) =>
                      try {
                        ( {
                          vLambda_17: ( Tuple2[Int, Tuple2[Int, Tuple2[Unit, Unit]]] => Exception ) =>
                            ( {
                              vLambda_18: ( Int => Tuple2[Int, Tuple2[Unit, Unit]] ) =>
                                ( {
                                  vLambda_0: Tuple2[Int, Tuple2[Unit, Unit]] =>
                                    ( {
                                      vLambda_1: Tuple2[Int, Tuple2[Unit, Unit]] =>
                                        try {
                                          ( {
                                            vLambda_17: ( Tuple2[Int, Tuple2[Int, Tuple2[Unit, Unit]]] => Exception ) =>
                                              pair[Int, Tuple2[Int, Tuple2[Unit, Unit]]]( pi1[Int, Tuple2[Unit, Unit]]( vLambda_0 ) )( pair[Int, Tuple2[Unit, Unit]]( pi1[Int, Tuple2[Unit, Unit]]( vLambda_1 ) )( ( {
                                                vLambda_10: Unit =>
                                                  ( {
                                                    vLambda_15: Unit =>
                                                      ( {
                                                        vLambda_9: Unit =>
                                                          ( {
                                                            vLambda_4: Unit =>
                                                              pair[Unit, Unit]( ( {
                                                                vLambda_5: ( Int => ( Unit => Unit ) ) =>
                                                                  ( {
                                                                    vLambda_3: ( Unit => Unit ) =>
                                                                      ( {
                                                                        vLambda_2: Unit => vLambda_2
                                                                      } )( vLambda_3( vLambda_4 ) )
                                                                  } )( vLambda_5( pi1[Int, Tuple2[Unit, Unit]]( vLambda_1 ) ) )
                                                              } )( vLambda_6( pi1[Int, Tuple2[Unit, Unit]]( vLambda_0 ) ) ) )( ( {
                                                                vLambda_12: ( Int => ( Int => ( Tuple2[Unit, Unit] => Unit ) ) ) =>
                                                                  ( {
                                                                    vLambda_11: ( Int => ( Tuple2[Unit, Unit] => Unit ) ) =>
                                                                      ( {
                                                                        vLambda_8: ( Tuple2[Unit, Unit] => Unit ) =>
                                                                          ( {
                                                                            vLambda_7: Unit => vLambda_7
                                                                          } )( vLambda_8( pair[Unit, Unit]( vLambda_9 )( vLambda_10 ) ) )
                                                                      } )( vLambda_11( pi1[Int, Tuple2[Unit, Unit]]( vLambda_1 ) ) )
                                                                  } )( vLambda_12( pi1[Int, Tuple2[Unit, Unit]]( vLambda_0 ) ) )
                                                              } )( vLambda_13( 0 ) ) )
                                                          } )( pi1[Unit, Unit]( pi2[Int, Tuple2[Unit, Unit]]( vLambda_1 ) ) )
                                                      } )( pi2[Unit, Unit]( pi2[Int, Tuple2[Unit, Unit]]( vLambda_1 ) ) )
                                                  } )( pi1[Unit, Unit]( pi2[Int, Tuple2[Unit, Unit]]( vLambda_0 ) ) )
                                              } )( pi2[Unit, Unit]( pi2[Int, Tuple2[Unit, Unit]]( vLambda_0 ) ) ) ) )
                                          } )( exception[Tuple2[Int, Tuple2[Int, Tuple2[Unit, Unit]]]]( _ )( Some( 1 ) ) )
                                        } catch {
                                          case Exn( v: Tuple2[Int, Tuple2[Int, Tuple2[Unit, Unit]]], Some( id ) ) if id == 1 => {
                                            //println( "thrown at " + e.id + " caught at 1" )
                                            ( {
                                              vLambda: Tuple2[Int, Tuple2[Int, Tuple2[Unit, Unit]]] => vLambda
                                            } )( v )
                                          }
                                          case e => {
                                            //println("throwing further at 1")
                                            throw e
                                          }
                                        }
                                    } )( vLambda_18( s( pi1[Int, Tuple2[Unit, Unit]]( vLambda_0 ) ) ) )
                                } )( vLambda_18( 0 ) )
                            } )(
                              try {
                                ( {
                                  vLambda_29: ( ( Int => Tuple2[Int, Tuple2[Unit, Unit]] ) => Exception ) =>
                                    efq[( Int => Tuple2[Int, Tuple2[Unit, Unit]] )]( vLambda_17( ( {
                                      vLambda_28: ( Int => Tuple2[Int, Tuple2[Unit, Unit]] ) =>
                                        ( {
                                          vLambda_19: Tuple2[Int, Tuple2[Unit, Unit]] =>
                                            ( {
                                              vLambda_20: Tuple2[Int, Tuple2[Unit, Unit]] =>
                                                try {
                                                  ( {
                                                    vLambda_17: ( Tuple2[Int, Tuple2[Int, Tuple2[Unit, Unit]]] => Exception ) =>
                                                      pair[Int, Tuple2[Int, Tuple2[Unit, Unit]]]( pi1[Int, Tuple2[Unit, Unit]]( vLambda_19 ) )( pair[Int, Tuple2[Unit, Unit]]( pi1[Int, Tuple2[Unit, Unit]]( vLambda_20 ) )( ( {
                                                        vLambda_23: Unit =>
                                                          ( {
                                                            vLambda_15: Unit =>
                                                              ( {
                                                                vLambda_22: Unit =>
                                                                  ( {
                                                                    vLambda_4: Unit =>
                                                                      pair[Unit, Unit]( ( {
                                                                        vLambda_5: ( Int => ( Unit => Unit ) ) =>
                                                                          ( {
                                                                            vLambda_3: ( Unit => Unit ) =>
                                                                              ( {
                                                                                vLambda_2: Unit => vLambda_2
                                                                              } )( vLambda_3( vLambda_4 ) )
                                                                          } )( vLambda_5( pi1[Int, Tuple2[Unit, Unit]]( vLambda_20 ) ) )
                                                                      } )( vLambda_6( pi1[Int, Tuple2[Unit, Unit]]( vLambda_19 ) ) ) )( ( {
                                                                        vLambda_25: ( Int => ( Int => ( Tuple2[Unit, Unit] => Unit ) ) ) =>
                                                                          ( {
                                                                            vLambda_24: ( Int => ( Tuple2[Unit, Unit] => Unit ) ) =>
                                                                              ( {
                                                                                vLambda_21: ( Tuple2[Unit, Unit] => Unit ) =>
                                                                                  ( {
                                                                                    vLambda_7: Unit => vLambda_7
                                                                                  } )( vLambda_21( pair[Unit, Unit]( vLambda_22 )( vLambda_23 ) ) )
                                                                              } )( vLambda_24( pi1[Int, Tuple2[Unit, Unit]]( vLambda_20 ) ) )
                                                                          } )( vLambda_25( pi1[Int, Tuple2[Unit, Unit]]( vLambda_19 ) ) )
                                                                      } )( vLambda_13( s( 0 ) ) ) )
                                                                  } )( pi1[Unit, Unit]( pi2[Int, Tuple2[Unit, Unit]]( vLambda_20 ) ) )
                                                              } )( pi2[Unit, Unit]( pi2[Int, Tuple2[Unit, Unit]]( vLambda_20 ) ) )
                                                          } )( pi1[Unit, Unit]( pi2[Int, Tuple2[Unit, Unit]]( vLambda_19 ) ) )
                                                      } )( pi2[Unit, Unit]( pi2[Int, Tuple2[Unit, Unit]]( vLambda_19 ) ) ) ) )
                                                  } )( exception[Tuple2[Int, Tuple2[Int, Tuple2[Unit, Unit]]]]( _ )( Some( 3 ) ) )
                                                } catch {
                                                  case Exn( v: Tuple2[Int, Tuple2[Int, Tuple2[Unit, Unit]]], Some( id ) ) if id == 3 => {
                                                    //println( "thrown at " + e.id + " caught at 3" )
                                                    ( {
                                                      vLambda: Tuple2[Int, Tuple2[Int, Tuple2[Unit, Unit]]] => vLambda
                                                    } )( v )
                                                  }
                                                  case e => {
                                                    //println("throwing further at 3")
                                                    throw e
                                                  }
                                                }
                                            } )( vLambda_28( s( pi1[Int, Tuple2[Unit, Unit]]( vLambda_19 ) ) ) )
                                        } )( vLambda_28( 0 ) )
                                    } )(
                                      try {
                                        ( {
                                          vLambda_30: ( ( Int => Tuple2[Int, Tuple2[Unit, Unit]] ) => Exception ) =>
                                            try {
                                              ( {
                                                vLambda_30: ( ( Int => Tuple2[Int, Tuple2[Unit, Unit]] ) => Exception ) =>
                                                  efq[( Int => Tuple2[Int, Tuple2[Unit, Unit]] )]( vLambda_29(
                                                    try {
                                                      ( {
                                                        vLambda_29: ( ( Int => Tuple2[Int, Tuple2[Unit, Unit]] ) => Exception ) =>
                                                          efq[( Int => Tuple2[Int, Tuple2[Unit, Unit]] )]( vLambda_30( ( {
                                                            n_ : Int =>
                                                              try {
                                                                ( {
                                                                  vLambda_32: ( Tuple2[Int, Tuple2[Unit, Unit]] => Exception ) =>
                                                                    efq[Tuple2[Int, Tuple2[Unit, Unit]]]( vLambda_29(
                                                                      try {
                                                                        ( {
                                                                          vLambda_29: ( ( Int => Tuple2[Int, Tuple2[Unit, Unit]] ) => Exception ) =>
                                                                            try {
                                                                              ( {
                                                                                vLambda_29: ( ( Int => Tuple2[Int, Tuple2[Unit, Unit]] ) => Exception ) =>
                                                                                  efq[( Int => Tuple2[Int, Tuple2[Unit, Unit]] )]( vLambda_32(
                                                                                    try {
                                                                                      ( {
                                                                                        vLambda_32: ( Tuple2[Int, Tuple2[Unit, Unit]] => Exception ) =>
                                                                                          efq[Tuple2[Int, Tuple2[Unit, Unit]]]( vLambda_29( ( {
                                                                                            n: Int =>
                                                                                              pair[Int, Tuple2[Unit, Unit]]( max( n )( n_ ) )(
                                                                                                try {
                                                                                                  ( {
                                                                                                    vLambda_38: ( Tuple2[Unit, Unit] => Exception ) =>
                                                                                                      efq[Tuple2[Unit, Unit]]( vLambda_32( pair[Int, Tuple2[Unit, Unit]]( max( n )( n_ ) )( pair[Unit, Unit]( ( {
                                                                                                        vLambda_35: ( Int => Unit ) =>
                                                                                                          ( {
                                                                                                            vLambda_34: Unit => vLambda_34
                                                                                                          } )( vLambda_35( n ) )
                                                                                                      } )( vLambda_36( n_ ) ) )(
                                                                                                        try {
                                                                                                          ( {
                                                                                                            vLambda_44: ( Unit => Exception ) =>
                                                                                                              efq[Unit]( vLambda_38( pair[Unit, Unit]( ( {
                                                                                                                vLambda_40: ( Int => Unit ) =>
                                                                                                                  ( {
                                                                                                                    vLambda_39: Unit => vLambda_39
                                                                                                                  } )( vLambda_40( n ) )
                                                                                                              } )( vLambda_41( n_ ) ) )( ( {
                                                                                                                vLambda_42: Sum[Unit, Unit] =>
                                                                                                                  matchSum( vLambda_42 )( ( {
                                                                                                                    vLambda_43: Unit => vLambda_43
                                                                                                                  } ) )( ( {
                                                                                                                    vLambda_37: Unit => efq[Unit]( vLambda_44( vLambda_37 ) )
                                                                                                                  } ) )
                                                                                                              } )( vLambda_45( max( n )( n_ ) ) ) ) ) )
                                                                                                          } )( exception[Unit]( _ )( Some( 12 ) ) )
                                                                                                        } catch {
                                                                                                          case Exn( v: Unit, Some( id ) ) if id == 12 => {
                                                                                                            //println( "thrown at " + e.id + " caught at 12" )
                                                                                                            ( {
                                                                                                              vLambda_37: Unit => vLambda_37
                                                                                                            } )( v )
                                                                                                          }
                                                                                                          case e => {
                                                                                                            //println("throwing further at 12")
                                                                                                            throw e
                                                                                                          }
                                                                                                        } ) ) ) )
                                                                                                  } )( exception[Tuple2[Unit, Unit]]( _ )( Some( 11 ) ) )
                                                                                                } catch {
                                                                                                  case Exn( v: Tuple2[Unit, Unit], Some( id ) ) if id == 11 => {
                                                                                                    //println( "thrown at " + e.id + " caught at 11" )
                                                                                                    ( {
                                                                                                      vLambda_33: Tuple2[Unit, Unit] => vLambda_33
                                                                                                    } )( v )
                                                                                                  }
                                                                                                  case e => {
                                                                                                    //println("throwing further at 11")
                                                                                                    throw e
                                                                                                  }
                                                                                                } )
                                                                                          } ) ) )
                                                                                      } )( exception[Tuple2[Int, Tuple2[Unit, Unit]]]( _ )( Some( 10 ) ) )
                                                                                    } catch {
                                                                                      case Exn( v: Tuple2[Int, Tuple2[Unit, Unit]], Some( id ) ) if id == 10 => {
                                                                                        //println( "thrown at " + e.id + " caught at 10" )
                                                                                        ( {
                                                                                          vLambda_31: Tuple2[Int, Tuple2[Unit, Unit]] => vLambda_31
                                                                                        } )( v )
                                                                                      }
                                                                                      case e => {
                                                                                        //println("throwing further at 10")
                                                                                        throw e
                                                                                      }
                                                                                    } ) )
                                                                              } )( exception[( Int => Tuple2[Int, Tuple2[Unit, Unit]] )]( _ )( Some( 9 ) ) )
                                                                            } catch {
                                                                              case Exn( v: ( Int => Tuple2[Int, Tuple2[Unit, Unit]] ), Some( id ) ) if id == 9 => {
                                                                                //println( "thrown at " + e.id + " caught at 9" )
                                                                                ( {
                                                                                  vLambda_18: ( Int => Tuple2[Int, Tuple2[Unit, Unit]] ) => vLambda_18
                                                                                } )( v )
                                                                              }
                                                                              case e => {
                                                                                //println("throwing further at 9")
                                                                                throw e
                                                                              }
                                                                            }
                                                                        } )( exception[( Int => Tuple2[Int, Tuple2[Unit, Unit]] )]( _ )( Some( 8 ) ) )
                                                                      } catch {
                                                                        case Exn( v: ( Int => Tuple2[Int, Tuple2[Unit, Unit]] ), Some( id ) ) if id == 8 => {
                                                                          //println( "thrown at " + e.id + " caught at 8" )
                                                                          ( {
                                                                            vLambda_18: ( Int => Tuple2[Int, Tuple2[Unit, Unit]] ) => vLambda_18
                                                                          } )( v )
                                                                        }
                                                                        case e => {
                                                                          //println("throwing further at 8")
                                                                          throw e
                                                                        }
                                                                      } ) )
                                                                } )( exception[Tuple2[Int, Tuple2[Unit, Unit]]]( _ )( Some( 7 ) ) )
                                                              } catch {
                                                                case Exn( v: Tuple2[Int, Tuple2[Unit, Unit]], Some( id ) ) if id == 7 => {
                                                                  //println( "thrown at " + e.id + " caught at 7" )
                                                                  ( {
                                                                    vLambda_31: Tuple2[Int, Tuple2[Unit, Unit]] => vLambda_31
                                                                  } )( v )
                                                                }
                                                                case e => {
                                                                  //println("throwing further at 7")
                                                                  throw e
                                                                }
                                                              }
                                                          } ) ) )
                                                      } )( exception[( Int => Tuple2[Int, Tuple2[Unit, Unit]] )]( _ )( Some( 6 ) ) )
                                                    } catch {
                                                      case Exn( v: ( Int => Tuple2[Int, Tuple2[Unit, Unit]] ), Some( id ) ) if id == 6 => {
                                                        //println( "thrown at " + e.id + " caught at 6" )
                                                        ( {
                                                          vLambda_18: ( Int => Tuple2[Int, Tuple2[Unit, Unit]] ) => vLambda_18
                                                        } )( v )
                                                      }
                                                      case e => {
                                                        //println("throwing further at 6")
                                                        throw e
                                                      }
                                                    } ) )
                                              } )( exception[( Int => Tuple2[Int, Tuple2[Unit, Unit]] )]( _ )( Some( 5 ) ) )
                                            } catch {
                                              case Exn( v: ( Int => Tuple2[Int, Tuple2[Unit, Unit]] ), Some( id ) ) if id == 5 => {
                                                //println( "thrown at " + e.id + " caught at 5" )
                                                ( {
                                                  vLambda_28: ( Int => Tuple2[Int, Tuple2[Unit, Unit]] ) => vLambda_28
                                                } )( v )
                                              }
                                              case e => {
                                                //println("throwing further at 5")
                                                throw e
                                              }
                                            }
                                        } )( exception[( Int => Tuple2[Int, Tuple2[Unit, Unit]] )]( _ )( Some( 4 ) ) )
                                      } catch {
                                        case Exn( v: ( Int => Tuple2[Int, Tuple2[Unit, Unit]] ), Some( id ) ) if id == 4 => {
                                          //println( "thrown at " + e.id + " caught at 4" )
                                          ( {
                                            vLambda_28: ( Int => Tuple2[Int, Tuple2[Unit, Unit]] ) => vLambda_28
                                          } )( v )
                                        }
                                        case e => {
                                          //println("throwing further at 4")
                                          throw e
                                        }
                                      } ) ) )
                                } )( exception[( Int => Tuple2[Int, Tuple2[Unit, Unit]] )]( _ )( Some( 2 ) ) )
                              } catch {
                                case Exn( v: ( Int => Tuple2[Int, Tuple2[Unit, Unit]] ), Some( id ) ) if id == 2 => {
                                  //println( "thrown at " + e.id + " caught at 2" )
                                  ( {
                                    vLambda_18: ( Int => Tuple2[Int, Tuple2[Unit, Unit]] ) => vLambda_18
                                  } )( v )
                                }
                                case e => {
                                  //println("throwing further at 2")
                                  throw e
                                }
                              } )
                        } )( exception[Tuple2[Int, Tuple2[Int, Tuple2[Unit, Unit]]]]( _ )( Some( 0 ) ) )
                      } catch {
                        case Exn( v: Tuple2[Int, Tuple2[Int, Tuple2[Unit, Unit]]], Some( id ) ) if id == 0 => {
                          //println( "thrown at " + e.id + " caught at 0" )
                          ( {
                            vLambda: Tuple2[Int, Tuple2[Int, Tuple2[Unit, Unit]]] => vLambda
                          } )( v )
                        }
                        case e => {
                          //println("throwing further at 0")
                          throw e
                        }
                      }
                  } )
              } )
          } )
      } )
  } )
}

object manualExistsMinimum extends Script {

  import gapt.expr._
  import gapt.formats.babel.{ Notation, Precedence }
  import gapt.proofs.context.Context
  import gapt.proofs.nd._

  implicit var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += Notation.Infix( "<", Precedence.infixRel )
  ctx += Notation.Infix( "<=", Precedence.infixRel )
  ctx += hoc"'<': nat>nat>o"
  ctx += hoc"'<=': nat>nat>o"
  ctx += hoc"'f': nat>nat"
  ctx += hof"lesseqf (n:nat) = (?x (f(x) <= n))"
  ctx += hof"lessf (n:nat) = (?x (f(x) < n))"
  ctx += hof"hasminf = (?y (-lessf(y) & lesseqf(y)))"
  val hasminf = hof"(?y (-lessf(y) & lesseqf(y)))"

  val lem1 = hof"!x!y (x < s(y) -> x <= y)"
  val lem2 = hof"!x (x <= 0 -> x = 0)"
  val lem3 = hof"!x (x = 0 -> -(?y f(y) < x))"

  val T1 = ProofBuilder.
    c( LogicalAxiom( hof"-lessf( s( n ) )" ) ).
    c( LogicalAxiom( hof"lesseqf( s( n ) )" ) ).
    b( AndIntroRule( _, _ ) ).
    u( ExistsIntroRule( _, hasminf ) ).
    u( DefinitionRule( _, hof"hasminf" ) ).
    qed
  //prooftool( T1 )

  val T2 = ProofBuilder.
    c( LogicalAxiom( hof"lessf(s(n))" ) ).
    u( DefinitionRule( _, hof"?x (f(x) < s(n))" ) ).
    c( LogicalAxiom( hof"lesseqf(n) -> hasminf" ) ).
    c( LogicalAxiom( lem1 ) ).
    u( ForallElimBlock( _, List( le"f(x)", le"(n:nat)" ) ) ).
    c( LogicalAxiom( hof"f(x) < s(n)" ) ).
    b( ImpElimRule( _, _ ) ).
    u( ExistsIntroRule( _, hof"?x (f(x) <= n)" ) ).
    u( DefinitionRule( _, hof"lesseqf(n)" ) ).
    b( ImpElimRule( _, _ ) ).
    b( ExistsElimRule( _, _ ) ).
    qed
  //prooftool( T2 )

  val step = ProofBuilder.
    c( T2 ).
    c( T1 ).
    b( ExcludedMiddleRule( _, _ ) ).
    u( ImpIntroRule( _, hof"lesseqf(s(n))" ) ).
    //u( ImpIntroRule( _, hof"lesseqf(n) -> hasminf" ) ).
    //u( ForallIntroRule( _, hof"!n ((lesseqf(n) -> hasminf) -> (lesseqf(s(n)) -> hasminf))", hov"(n:nat)" ) ).
    qed
  prooftool( step )
  val icStep = InductionCase( step, hoc"s", List( step.endSequent.indexOfInAnt( hof"lesseqf(n) -> hasminf" ) ), List( hov"n:nat" ) )

  val base = ProofBuilder.
    c( LogicalAxiom( hof"lesseqf(0)" ) ).
    u( DefinitionRule( _, hof"?x (f(x) <= 0)" ) ).
    c( LogicalAxiom( lem3 ) ).
    u( ForallElimRule( _, le"f(x)" ) ).
    c( LogicalAxiom( lem2 ) ).
    u( ForallElimRule( _, le"f(x)" ) ).
    c( LogicalAxiom( hof"f(x) <= 0" ) ).
    b( ImpElimRule( _, _ ) ).
    b( ImpElimRule( _, _ ) ).
    u( DefinitionRule( _, hof"-lessf(f(z))" ) ).
    c( LogicalAxiom( hof"f(z) <= f(z)" ) ).
    u( ExistsIntroRule( _, hof"?x (f(x) <= f(z))" ) ).
    u( DefinitionRule( _, hof"lesseqf(f(z))" ) ).
    b( AndIntroRule( _, _ ) ).
    u( ExistsIntroRule( _, hasminf ) ).
    u( DefinitionRule( _, hof"hasminf" ) ).
    b( ExistsElimRule( _, _ ) ).
    u( ImpIntroRule( _, hof"lesseqf(0)" ) ).
    qed
  prooftool( base )
  val icBase = InductionCase( base, hoc"0:nat", List.empty, List.empty )

  val proof = ProofBuilder.
    c( InductionRule( List( icBase, icStep ), Abs( hov"n:nat", hof"lesseqf(n) -> hasminf" ), le"n:nat" ) ).
    u( ForallIntroRule( _, hov"n:nat", hov"n:nat" ) ).
    u( ForallElimRule( _, le"f(0)" ) ).
    c( LogicalAxiom( hof"f(0) <= f(0)" ) ).
    u( ExistsIntroRule( _, hof"?x (x <= f(0))" ) ).
    u( DefinitionRule( _, hof"lesseqf(f(0))" ) ).
    b( ImpElimRule( _, _ ) ).
    qed
  prooftool( proof )
  import extraction.{ ScalaCodeGenerator, FSharpCodeGenerator }
  //val m1 = ClassicalExtraction.extractCases( eliminateDefinitions( proof ) )
  //ScalaCodeGenerator( m1 )( ClassicalExtraction.systemT( ctx ) )
}

/*
object coquand extends Script {

def s( x: Int ) = x + 1
def leq( x: Int )( y: Int ) = x <= y
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

//def natRec[( Tuple2[Int, Unit] => Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] )]( p1: A )( p2: ( Int => A => A ) )( p3: Int ): A = {
def natRec[A]( p1: A )( p2: ( Int => A => A ) )( p3: Int ): A = {
  println( s"in natRec: $p1, $p3" )
  if ( p3 == 0 ) {
    p1
  } else {
    p2( p3 - 1 )( natRec( p1 )( p2 )( p3 - 1 ) )
  }
}

case class Exn[A]( v: A, id: Option[Int] ) extends Exception
def exception[A]( v: A )( id: Option[Int] = None ) = {
  println( s"in exception: $v" )
  new Exn( v, id )
}
def pi1[A, B]( p: ( A, B ) ) = p._1
def add( x: Int )( y: Int ) = x + y
def pair[A, B]( p0: A )( p1: B ): Tuple2[A, B] = ( p0, p1 )
def efq[B]( p: Throwable ): B = throw p

//def f( x: Int ) = if ( x > 5 ) 1 else 5 - ( x + 1 )
def f( x: Int ) = if ( x == 0 ) 1 else if ( x == 1 ) 2 else 0

val hasminProgram = ( {
  vLambda_10: Unit =>
    ( {
      vLambda_6: ( Int => ( Int => ( Unit => Unit ) ) ) =>
        ( {
          vLambda_3: ( Int => Unit ) =>
            ( {
              vLambda_1: ( Int => ( Unit => Unit ) ) =>
                ( {
                  vLambda_0: ( Int => ( Unit => ( Tuple2[Int, Unit] => Exception ) ) ) =>
                    ( {
                      val F: Int => Tuple2[Int, Unit] => ( Int, ( Tuple2[Int, Unit] => Exception, Tuple2[Int, Unit] ) ) = ( {
                        n: Int =>
                          natRec[( Tuple2[Int, Unit] => Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] )]( {
                            val base = ( {
                              vLambda: Tuple2[Int, Unit] => pair[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]( f( pi1[Int, Unit]( vLambda ) ) )( pair[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]( vLambda_0( f( pi1[Int, Unit]( vLambda ) ) )( vLambda_1( f( pi1[Int, Unit]( vLambda ) ) )( pi2[Int, Unit]( vLambda ) ) ) )( pair[Int, Unit]( pi1[Int, Unit]( vLambda ) )( vLambda_3( f( pi1[Int, Unit]( vLambda ) ) ) ) ) )
                            } )
                            base
                          } )( {
                            println( "step case" )
                            ( {
                              n: Int => // n is the recursion counter
                                ( {
                                  vLambda_5: ( Tuple2[Int, Unit] => Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] ) => // vLambda_5 is the previous result of the recursion
                                    ( {
                                      vLambda_9: Tuple2[Int, Unit] =>
                                        try {
                                          println( s"in try: n=$n" )
                                          val T = ( {
                                            vLambda_8: ( Tuple2[Int, Unit] => Exception ) => pair[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]( s( n ) )( pair[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]( vLambda_8 )( vLambda_9 ) )
                                          } )
                                          println( "after definition of T" )
                                          val ret = T( exception[Tuple2[Int, Unit]]( _ )( Some( 0 ) ) )
                                          println( s"after definition of ret: $ret" )
                                          ret
                                        } catch {
                                          case Exn( v: Tuple2[Int, Unit], Some( id ) ) if id == 0 => {
                                            println( "thrown at " + id + " caught at 0" )
                                            ( {
                                              vLambda_4: Tuple2[Int, Unit] => vLambda_5( pair[Int, Unit]( pi1[Int, Unit]( vLambda_4 ) )( vLambda_6( f( pi1[Int, Unit]( vLambda_4 ) ) )( n )( pi2[Int, Unit]( vLambda_4 ) ) ) )
                                            } )( v )
                                          }
                                          case e => {
                                            println( "throwing further at 0" )
                                            throw e
                                          }
                                        }
                                    } )
                                } )
                            } )
                          } )( n )
                      } )
                      println( "applying f(0) to F" )
                      val retF = F( f( 0 ) ) // forall-elim f(0)
                      println( "after definition of retF" )
                      retF
                    } )( pair[Int, Unit]( 0 )( vLambda_10 ) ) // exists-intro 0, imp-elim
                } )
            } )
        } )
    } )
} )

val arg1 = {
  _: Int =>
    {
      _: Int =>
        {
          _: Unit =>
            {
              ()
            }
        }
    }
}
val arg2 = {
  _: Int =>
    {
      ()
    }
}
val arg3 = {
  _: Int =>
    {
      _: Unit =>
        {
          ()
        }
    }
}
//val lem3 = hof"!x (x = 0 -> -(?y f(y) < x))"
val arg4 = {
  x: Int =>
    {
      y: Unit =>
        {
          arg: Tuple2[Int, Unit] =>
            {
              println( "in arg4" )
              exception( arg )( None )
            }
        }
    }
}
val realHasminProgram = hasminProgram()( arg1 )( arg2 )( arg3 )( arg4 )
val res = realHasminProgram
println( s"res: $res" )

val coquandProgram = ( {
  vLambda_3: ( Int => ( ( Tuple2[Int, Unit] => Exception ) => ( Int => Unit ) ) ) =>
    ( {
      vLambda_1: ( Int => ( Int => ( Int => ( Tuple2[Unit, Unit] => Unit ) ) ) ) =>
        ( {
          vLambda: Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] =>
            ( {
              a: Int => pair[Int, Unit]( pi1[Int, Unit]( pi2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]( pi2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]( vLambda ) ) ) )( vLambda_1( f( pi1[Int, Unit]( pi2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]( pi2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]( vLambda ) ) ) ) )( pi1[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]( vLambda ) )( f( add( pi1[Int, Unit]( pi2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]( pi2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]( vLambda ) ) ) )( a ) ) )( pair[Unit, Unit]( pi2[Int, Unit]( pi2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]( pi2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]( vLambda ) ) ) )( vLambda_3( pi1[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]( vLambda ) )( pi1[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]( pi2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]( vLambda ) ) )( add( pi1[Int, Unit]( pi2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]( pi2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]( vLambda ) ) ) )( a ) ) ) ) )
            } )
        } )
    } )
} )

val arg5 = {
  x: Int =>
    {
      y: ( Tuple2[Int, Unit] => Exception ) =>
        {
          { _: Int => () }
        }
    }
}
val arg6 = {
  _: Int =>
    {
      _: Int =>
        {
          _: Int =>
            {
              { _: Tuple2[Unit, Unit] => () }
            }
        }
    }
}
val realCoquandProgram: Int => ( Int, Unit ) = coquandProgram( arg5 )( arg6 )( realHasminProgram )

0 to 1 foreach ( i => println( s"realCoquandProgram($i): ${realCoquandProgram( i )}" ) )

}
*/

object coquandConstructive extends Script {

  def s( x: Int ) = x + 1

  def leq( x: Int )( y: Int ) = x <= y

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
      println( "base case" )
      p1
    } else {
      println( s"step case ${p3 - 1}" )
      p2( p3 - 1 )( natRec( p1 )( p2 )( p3 - 1 ) )
    }
  }

  case class Exn[A]( v: A, id: Option[Int] ) extends Exception

  def exception[A]( v: A )( id: Option[Int] = None ) = new Exn( v, id )

  def existsElim[A, B, C]( p1: Tuple2[A, B] )( p2: A => B => C ) = {
    println( s"calling existsElim with $p1" )
    p2( p1._1 )( p1._2 )
  }

  def pi1[A, B]( p: ( A, B ) ) = p._1

  def add( x: Int )( y: Int ) = x + y

  def pair[A, B]( p0: A )( p1: B ): Tuple2[A, B] = ( p0, p1 )

  def efq[B]( p: Throwable ): B = throw p

  /*
// OK:
def f( x: Int ) = 2 * x
def f( x: Int ) = x + 1
def f( x: Int ) = 1
*/
  // NOT OK:
  def f( x: Int ) = if ( x > 5 ) 0 else 5 - x
  /*
def f( x: Int ) = {
  val ret = -( x * x ) + 2
  if ( ret < 0 ) 0 else ret
}
*/

  def hasminProgram =
    ( {
      vLambda_10: Unit =>
        ( {
          vLambda_6: ( Int => ( Int => ( Unit => Unit ) ) ) =>
            ( {
              vLambda_3: ( Int => Unit ) =>
                ( {
                  vLambda_1: ( Int => ( Unit => Unit ) ) =>
                    ( {
                      vLambda_0: ( Int => ( Unit => ( Tuple2[Int, Unit] => Exception ) ) ) =>
                        ( {
                          n: Int =>
                            val retNatRec = natRec[( Tuple2[Int, Unit] => Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] )]( ( { // Base Case: A
                              vLambda: Tuple2[Int, Unit] =>
                                println( "before existsElim 1" )
                                val ret = existsElim[Int, Unit, Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]]( vLambda )( ( {
                                  z: Int =>
                                    ( {
                                      vLambda_2: Unit =>
                                        pair[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]( f( z ) )( pair[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]( {
                                          val ftmp = vLambda_0( f( z ) ); println( "ftmp" ); ftmp( vLambda_1( f( z ) )( vLambda_2 ) )
                                        } )( pair[Int, Unit]( z )( vLambda_3( f( z ) ) ) ) )
                                    } )
                                } ) )
                                println( "after existsElim 1" )
                                ret
                            } ) )( ( { // Step Case: Int -> A -> A
                              n: Int =>
                                ( {
                                  vLambda_5: ( Tuple2[Int, Unit] => Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] ) =>
                                    ( {
                                      vLambda_9: Tuple2[Int, Unit] => // exists x (f(x) <= s(n))
                                        try {
                                          println( s"in try: $n" )
                                          ( {
                                            vLambda_8: ( Tuple2[Int, Unit] => Exception ) =>
                                              pair[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]( s( n ) )( pair[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]( vLambda_8 )( {
                                                println( s"consuming vLambda_9: $vLambda_9" ); vLambda_9
                                              } ) )
                                          } )( exception[Tuple2[Int, Unit]]( _ )( Some( 0 ) ) )
                                          //throw tmp._2._1( vLambda_9 )
                                        } catch {
                                          case Exn( v: Tuple2[Int, Unit], Some( id ) ) if id == 0 => {
                                            println( s"thrown at $id caught at 0: $v" )
                                            ( {
                                              vLambda_4: Tuple2[Int, Unit] =>
                                                existsElim[Int, Unit, Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]]( vLambda_4 )( ( {
                                                  x: Int =>
                                                    ( {
                                                      vLambda_7: Unit => vLambda_5( pair[Int, Unit]( x )( vLambda_6( f( x ) )( n )( vLambda_7 ) ) )
                                                    } )
                                                } ) )
                                            } )( v )
                                          }
                                          case e => {
                                            println( "throwing further at 0" )
                                            throw e
                                          }
                                        }
                                    } )
                                } )
                            } ) )( n )
                            println( "after natRec" )
                            retNatRec
                        } )( f( 0 ) )( pair[Int, Unit]( 0 )( vLambda_10 ) )
                    } )
                } )
            } )
        } )
    } )

  val arg1 = {
    _: Int =>
      {
        _: Int =>
          {
            _: Unit =>
              {
                ()
              }
          }
      }
  }
  val arg2 = {
    _: Int =>
      {
        ()
      }
  }
  val arg3 = {
    _: Int =>
      {
        _: Unit =>
          {
            ()
          }
      }
  }
  //val lem3 = hof"!x (x = 0 -> -(?y f(y) < x))"
  val arg4 = {
    x: Int =>
      {
        y: Unit =>
          {
            arg: Tuple2[Int, Unit] =>
              {
                println( "in arg4" )
                exception( arg )( None )
              }
          }
      }
  }
  val realHasminProgram = hasminProgram()( arg1 )( arg2 )( arg3 )( arg4 )
  //val res = realHasminProgram
  //println( s"res: $res" )
  //val min = res._1
  //val min = 0
  /*
if ( !( ( 0 to 1000 forall ( x => f( x ) >= min ) ) && ( 0 to 1000 exists ( x => f( x ) <= min ) ) ) ) {
  println( s"minimum ${min} incorrect" )
  assert( false )
} else {
  println( s"minimum ${min} correct" )
}
*/

  // constructive proof of -?x Px -> !x -Px
  val coquandProgram = ( {
    vLambda_3: ( Int => ( Int => ( ( Unit => Exception ) => Unit ) ) ) =>
      ( {
        vLambda_1: ( Int => ( Int => ( Int => ( Tuple2[Unit, Unit] => Unit ) ) ) ) =>
          ( {
            vLambda: Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] =>
              existsElim[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]], ( Int => Tuple2[Int, Unit] )]( vLambda )( ( {
                y: Int =>
                  ( {
                    vLambda_0: Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]] =>
                      existsElim[Int, Unit, ( Int => Tuple2[Int, Unit] )]( pi2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]( vLambda_0 ) )( ( {
                        x: Int =>
                          println( s"x: $x" )
                          ( {
                            vLambda_2: Unit =>
                              ( {
                                a: Int =>
                                  println( s"x: $x, a: $a" )
                                  pair[Int, Unit]( x )( vLambda_1( f( x ) )( y )( f( add( x )( a ) ) )( pair[Unit, Unit]( vLambda_2 )( ( {
                                    y: Int =>
                                      ( {
                                        vLambda_4: ( Tuple2[Int, Unit] => Exception ) =>
                                          ( {
                                            x: Int =>
                                              println( s"x: $x, y: $y" )
                                              vLambda_3( f( x ) )( y )( ( {
                                                vLambda_5: Unit => vLambda_4( pair[Int, Unit]( x )( vLambda_5 ) )
                                              } ) )
                                          } )
                                      } )
                                  } )( y )( pi1[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]( vLambda_0 ) )( add( x )( a ) ) ) ) )
                              } )
                          } )
                      } ) )
                  } )
              } ) )
          } )
      } )
  } )

  val arg5 = {
    _: Int =>
      {
        _: Int =>
          {
            f: ( Unit => Exception ) =>
              {
                f() // doesn't change outcome here
                ()
              }
          }
      }
  }
  val arg6 = {
    _: Int =>
      {
        _: Int =>
          {
            _: Int =>
              {
                { _: Tuple2[Unit, Unit] => () }
              }
          }
      }
  }

  println( s"realHasminProgram: $realHasminProgram" )
  val realCoquandProgram: Int => ( Int, Unit ) = coquandProgram( arg5 )( arg6 )( realHasminProgram )

  0 to 6 foreach ( i => println( s"realCoquandProgram($i): ${realCoquandProgram( i )}" ) )

}

object coquandConstructiveHypVars extends Script {

  def s( x: Int ) = x + 1

  def leq( x: Int )( y: Int ) = x <= y

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
      println( "base case" )
      p1
    } else {
      println( s"step case ${p3 - 1}" )
      p2( p3 - 1 )( natRec( p1 )( p2 )( p3 - 1 ) )
    }
  }

  case class Exn[A]( v: A, id: Option[Int] ) extends Exception

  def exception[A]( v: A )( id: Option[Int] = None ) = new Exn( v, id )

  def existsElim[A, B, C]( p1: Tuple2[A, B] )( p2: A => B => C ) = {
    println( s"calling existsElim with $p1" )
    p2( p1._1 )( p1._2 )
  }

  def pi1[A, B]( p: ( A, B ) ) = p._1

  def add( x: Int )( y: Int ) = x + y

  def pair[A, B]( p0: A )( p1: B ): Tuple2[A, B] = ( p0, p1 )

  def efq[B]( p: Throwable ): B = throw p

  def raise[A]( x: A ): ( Exception ) = throw exception( x )( None )

  /*
// OK:
def f( x: Int ) = 2 * x
def f( x: Int ) = x + 1
def f( x: Int ) = 1
*/
  // NOT OK:
  def f( x: Int ) = if ( x > 5 ) 0 else 5 - x
  /*
def f( x: Int ) = {
  val ret = -( x * x ) + 2
  if ( ret < 0 ) 0 else ret
}
*/

  def hasminProgram = ( {
    vLambda_6: Unit =>
      ( {
        vLambda_4: ( Int => ( Int => ( Unit => Unit ) ) ) =>
          ( {
            vLambda_2: ( Int => Unit ) =>
              ( {
                vLambda_0: ( Int => ( Unit => Unit ) ) =>
                  ( {
                    vLambda: ( Int => ( Unit => ( Tuple2[Int, Unit] => Exception ) ) ) =>
                      ( {
                        n: Int =>
                          natRec[( Tuple2[Int, Unit] => Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] )]( ( {
                            vHyp: Tuple2[Int, Unit] =>
                              existsElim[Int, Unit, Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]]( vHyp )( ( {
                                z: Int =>
                                  ( {
                                    vLambda_1: Unit => pair[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]( f( z ) )( pair[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]( vLambda( f( z ) )( vLambda_0( f( z ) )( vLambda_1 ) ) )( pair[Int, Unit]( z )( vLambda_2( f( z ) ) ) ) )
                                  } )
                              } ) )
                          } ) )( ( {
                            n: Int =>
                              ( {
                                vLambda_3: ( Tuple2[Int, Unit] => Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] ) =>
                                  ( {
                                    vHyp_2: Tuple2[Int, Unit] =>
                                      try {
                                        ( {
                                          vHyp_1: ( Tuple2[Int, Unit] => Exception ) => pair[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]( s( n ) )( pair[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]( raise )( vHyp_2 ) )
                                        } )( exception[Tuple2[Int, Unit]]( _ )( Some( 0 ) ) )
                                      } catch {
                                        case Exn( v: Tuple2[Int, Unit], Some( id ) ) if id == 0 => {
                                          //println( "thrown at " + id + " caught at 0" )
                                          ( {
                                            vHyp_0: Tuple2[Int, Unit] =>
                                              existsElim[Int, Unit, Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]]( vHyp_0 )( ( {
                                                x: Int =>
                                                  ( {
                                                    vLambda_5: Unit => vLambda_3( pair[Int, Unit]( x )( vLambda_4( f( x ) )( n )( vLambda_5 ) ) )
                                                  } )
                                              } ) )
                                          } )( v )
                                        }
                                        case e => {
                                          //println("throwing further at 0")
                                          throw e
                                        }
                                      }
                                  } )
                              } )
                          } ) )( n )
                      } )( f( 0 ) )( pair[Int, Unit]( 0 )( vLambda_6 ) )
                  } )
              } )
          } )
      } )
  } )

  val arg1 = {
    _: Int =>
      {
        _: Int =>
          {
            _: Unit =>
              {
                ()
              }
          }
      }
  }
  val arg2 = {
    _: Int =>
      {
        ()
      }
  }
  val arg3 = {
    _: Int =>
      {
        _: Unit =>
          {
            ()
          }
      }
  }
  //val lem3 = hof"!x (x = 0 -> -(?y f(y) < x))"
  val arg4 = {
    x: Int =>
      {
        y: Unit =>
          {
            arg: Tuple2[Int, Unit] =>
              {
                println( "in arg4" )
                exception( arg )( None )
              }
          }
      }
  }
  val realHasminProgram = hasminProgram()( arg1 )( arg2 )( arg3 )( arg4 )
  //val res = realHasminProgram
  //println( s"res: $res" )
  //val min = res._1
  //val min = 0
  /*
if ( !( ( 0 to 1000 forall ( x => f( x ) >= min ) ) && ( 0 to 1000 exists ( x => f( x ) <= min ) ) ) ) {
  println( s"minimum ${min} incorrect" )
  assert( false )
} else {
  println( s"minimum ${min} correct" )
}
*/

  // constructive proof of -?x Px -> !x -Px
  val coquandProgram = ( {
    vLambda_2: ( Int => ( Int => ( ( Unit => Exception ) => Unit ) ) ) =>
      ( {
        vLambda_0: ( Int => ( Int => ( Int => ( Tuple2[Unit, Unit] => Unit ) ) ) ) =>
          ( {
            vHyp: Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] =>
              existsElim[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]], ( Int => Tuple2[Int, Unit] )]( vHyp )( ( {
                y: Int =>
                  ( {
                    vLambda: Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]] =>
                      existsElim[Int, Unit, ( Int => Tuple2[Int, Unit] )]( pi2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]( vLambda ) )( ( {
                        x: Int =>
                          ( {
                            vLambda_1: Unit =>
                              ( {
                                a: Int =>
                                  pair[Int, Unit]( x )( vLambda_0( f( x ) )( y )( f( add( x )( a ) ) )( pair[Unit, Unit]( vLambda_1 )( ( {
                                    y: Int =>
                                      ( {
                                        vHyp_0: ( Tuple2[Int, Unit] => Exception ) =>
                                          ( {
                                            x: Int =>
                                              vLambda_2( f( x ) )( y )( ( {
                                                vLambda_3: Unit => raise( pair[Int, Unit]( x )( vLambda_3 ) )
                                              } ) )
                                          } )
                                      } )
                                  } )( y )( pi1[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]( vLambda ) )( add( x )( a ) ) ) ) )
                              } )
                          } )
                      } ) )
                  } )
              } ) )
          } )
      } )
  } )

  val arg5 = {
    _: Int =>
      {
        _: Int =>
          {
            f: ( Unit => Exception ) =>
              {
                //f() // how to implement this?
                ()
              }
          }
      }
  }
  val arg6 = {
    _: Int =>
      {
        _: Int =>
          {
            _: Int =>
              {
                { _: Tuple2[Unit, Unit] => () }
              }
          }
      }
  }

  println( s"realHasminProgram: $realHasminProgram" )
  val realCoquandProgram: Int => ( Int, Unit ) = coquandProgram( arg5 )( arg6 )( realHasminProgram )

  0 to 6 foreach ( i => println( s"realCoquandProgram($i): ${realCoquandProgram( i )}" ) )

}

object coquandClassical extends Script {

  def s( x: Int ) = x + 1

  def leq( x: Int )( y: Int ) = x <= y

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
      println( "base case" )
      p1
    } else {
      println( s"step case ${p3 - 1}" )
      p2( p3 - 1 )( natRec( p1 )( p2 )( p3 - 1 ) )
    }
  }

  case class Exn[A]( v: A, id: Option[Int] ) extends Exception

  def exception[A]( v: A )( id: Option[Int] = None ) = new Exn( v, id )

  def existsElim[A, B, C]( p1: Tuple2[A, B] )( p2: A => B => C ) = p2( p1._1 )( p1._2 )

  def pi1[A, B]( p: ( A, B ) ) = p._1

  def add( x: Int )( y: Int ) = x + y

  def pair[A, B]( p0: A )( p1: B ): Tuple2[A, B] = ( p0, p1 )

  def efq[B]( p: Throwable ): B = throw p

  /*
// OK:
def f( x: Int ) = 2 * x
def f( x: Int ) = x + 1
def f( x: Int ) = 1
*/
  // NOT OK:
  def f( x: Int ) = if ( x > 5 ) 0 else 5 - x
  /*
def f( x: Int ) = {
  val ret = -( x * x ) + 2
  if ( ret < 0 ) 0 else ret
}
*/

  def hasminProgram =
    ( {
      vLambda_10: Unit =>
        ( {
          vLambda_6: ( Int => ( Int => ( Unit => Unit ) ) ) =>
            ( {
              vLambda_3: ( Int => Unit ) =>
                ( {
                  vLambda_1: ( Int => ( Unit => Unit ) ) =>
                    ( {
                      vLambda_0: ( Int => ( Unit => ( Tuple2[Int, Unit] => Exception ) ) ) =>
                        ( {
                          n: Int =>
                            val retNatRec = natRec[( Tuple2[Int, Unit] => Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] )]( ( { // Base Case: A
                              vLambda: Tuple2[Int, Unit] =>
                                println( "before existsElim 1" )
                                val ret = existsElim[Int, Unit, Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]]( vLambda )( ( {
                                  z: Int =>
                                    ( {
                                      vLambda_2: Unit =>
                                        pair[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]( f( z ) )( pair[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]( {
                                          val ftmp = vLambda_0( f( z ) ); println( "ftmp" ); ftmp( vLambda_1( f( z ) )( vLambda_2 ) )
                                        } )( pair[Int, Unit]( z )( vLambda_3( f( z ) ) ) ) )
                                    } )
                                } ) )
                                println( "after existsElim 1" )
                                ret
                            } ) )( ( { // Step Case: Int -> A -> A
                              n: Int =>
                                ( {
                                  vLambda_5: ( Tuple2[Int, Unit] => Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] ) =>
                                    ( {
                                      vLambda_9: Tuple2[Int, Unit] => // exists x (f(x) <= s(n))
                                        try {
                                          println( s"in try: $n" )
                                          ( {
                                            vLambda_8: ( Tuple2[Int, Unit] => Exception ) =>
                                              pair[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]( s( n ) )( pair[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]( vLambda_8 )( {
                                                println( s"consuming vLambda_9: $vLambda_9" ); vLambda_9
                                              } ) )
                                          } )( exception[Tuple2[Int, Unit]]( _ )( Some( 0 ) ) )
                                          //throw tmp._2._1( vLambda_9 )
                                        } catch {
                                          case Exn( v: Tuple2[Int, Unit], Some( id ) ) if id == 0 => {
                                            println( s"thrown at $id caught at 0: $v" )
                                            ( {
                                              vLambda_4: Tuple2[Int, Unit] =>
                                                existsElim[Int, Unit, Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]]( vLambda_4 )( ( {
                                                  x: Int =>
                                                    ( {
                                                      vLambda_7: Unit => vLambda_5( pair[Int, Unit]( x )( vLambda_6( f( x ) )( n )( vLambda_7 ) ) )
                                                    } )
                                                } ) )
                                            } )( v )
                                          }
                                          case e => {
                                            println( "throwing further at 0" )
                                            throw e
                                          }
                                        }
                                    } )
                                } )
                            } ) )( n )
                            println( "after natRec" )
                            retNatRec
                        } )( f( 0 ) )( pair[Int, Unit]( 0 )( vLambda_10 ) )
                    } )
                } )
            } )
        } )
    } )

  val arg1 = {
    _: Int =>
      {
        _: Int =>
          {
            _: Unit =>
              {
                ()
              }
          }
      }
  }
  val arg2 = {
    _: Int =>
      {
        ()
      }
  }
  val arg3 = {
    _: Int =>
      {
        _: Unit =>
          {
            ()
          }
      }
  }
  //val lem3 = hof"!x (x = 0 -> -(?y f(y) < x))"
  val arg4 = {
    x: Int =>
      {
        y: Unit =>
          {
            arg: Tuple2[Int, Unit] =>
              {
                println( "in arg4" )
                exception( arg )( None )
              }
          }
      }
  }
  val realHasminProgram = hasminProgram()( arg1 )( arg2 )( arg3 )( arg4 )
  //val res = realHasminProgram
  //println( s"res: $res" )
  //val min = res._1
  //val min = 0
  /*
if ( !( ( 0 to 1000 forall ( x => f( x ) >= min ) ) && ( 0 to 1000 exists ( x => f( x ) <= min ) ) ) ) {
  println( s"minimum ${min} incorrect" )
  assert( false )
} else {
  println( s"minimum ${min} correct" )
}
*/

  // constructive proof of -?x Px -> !x -Px
  val coquandProgram = ( {
    vLambda_5: ( Int => ( Int => ( ( Unit => Exception ) => Unit ) ) ) =>
      ( {
        vLambda_1: ( Int => ( Int => ( Int => ( Tuple2[Unit, Unit] => Unit ) ) ) ) =>
          ( {
            vLambda: Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] =>
              existsElim[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]], ( Int => Tuple2[Int, Unit] )]( vLambda )( ( {
                y: Int =>
                  ( {
                    vLambda_0: Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]] => // vLambda_0 comes from -(?x (f(x) < y)) & (?x (f(x) <= y))
                      existsElim[Int, Unit, ( Int => Tuple2[Int, Unit] )]( pi2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]( vLambda_0 ) )( ( {
                        x: Int =>
                          ( {
                            vLambda_2: Unit =>
                              ( {
                                a: Int =>
                                  pair[Int, Unit]( x )( vLambda_1( f( x ) )( y )( f( add( x )( a ) ) )( pair[Unit, Unit]( vLambda_2 )( ( {
                                    y: Int =>
                                      ( {
                                        vLambda_4: ( Tuple2[Int, Unit] => Exception ) =>
                                          ( {
                                            x: Int =>
                                              try {
                                                ( {
                                                  vLambda_6: ( Unit => Exception ) => efq[Unit]( vLambda_4( pair[Int, Unit]( x )( vLambda_5( y )( f( x ) )( vLambda_6 ) ) ) )
                                                } )( exception[Unit]( _ )( Some( 1 ) ) )
                                              } catch {
                                                case Exn( v: Unit, Some( id ) ) if id == 1 => {
                                                  //println( "thrown at " + id + " caught at 0" )
                                                  ( {
                                                    vLambda_3: Unit => vLambda_3
                                                  } )( v )
                                                }
                                                case e @ Exn( v, Some( id ) ) => {
                                                  println( s"throwing further at 0, id $id" )
                                                  throw e
                                                }
                                              }
                                          } )
                                      } )
                                  } )( y )( pi1[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]( vLambda_0 ) )( add( x )( a ) ) ) ) )
                              } )
                          } )
                      } ) )
                  } )
              } ) )
          } )
      } )
  } )

  val arg5 = {
    _: Int =>
      {
        _: Int =>
          {
            _: ( Unit => Exception ) =>
              {
                ()
              }
          }
      }
  }
  val arg6 = {
    _: Int =>
      {
        _: Int =>
          {
            _: Int =>
              {
                { _: Tuple2[Unit, Unit] => () }
              }
          }
      }
  }

  val realCoquandProgram: Int => ( Int, Unit ) = coquandProgram( arg5 )( arg6 )( realHasminProgram )

  0 to 6 foreach ( i => println( s"realCoquandProgram($i): ${realCoquandProgram( i )}" ) )

}

object hasminExceptionTest extends Script {

  def s( x: Int ) = x + 1

  def leq( x: Int )( y: Int ) = x <= y

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
      println( "base case" )
      p1
    } else {
      println( "step case" )
      p2( p3 - 1 )( natRec( p1 )( p2 )( p3 - 1 ) )
    }
  }

  case class Exn[A]( v: A, id: Option[Int] ) extends Exception

  def exception[A]( v: A )( id: Option[Int] = None ) = new Exn( v, id )

  def existsElim[A, B, C]( p1: Tuple2[A, B] )( p2: A => B => C ) = p2( p1._1 )( p1._2 )

  def pi1[A, B]( p: ( A, B ) ) = p._1

  def add( x: Int )( y: Int ) = x + y

  def pair[A, B]( p0: A )( p1: B ): Tuple2[A, B] = ( p0, p1 )

  def efq[B]( p: Throwable ): B = {
    println( "THROWING NOW" )
    throw p
  }

  def f( x: Int ) = if ( x > 5 ) 0 else 5 - x
  val X0 = 0

  //def f( x: Int ) = 1

  val hasminProgram = ( {
    vLambda_30: ( Int => ( Unit => Unit ) ) =>
      ( {
        vLambda_28: ( Int => ( Unit => ( Tuple2[Int, Unit] => Exception ) ) ) =>
          ( {
            vLambda_26: ( Int => ( Int => ( Unit => Unit ) ) ) =>
              ( {
                vLambda_29: ( Int => Unit ) =>
                  ( {
                    vLambda_12: ( Unit => Unit ) =>
                      ( {
                        vLambda_13: Unit =>
                          ( {
                            vLambda_3: Unit =>
                              ( {
                                vLambda_10: ( Unit => ( Tuple2[Int, Unit] => Exception ) ) =>
                                  try {
                                    ( {
                                      vLambda_1: ( Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] => Exception ) =>
                                        pair[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]( 0 )(
                                          try {
                                            ( {
                                              vLambda_5: ( Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]] => Exception ) =>
                                                efq[Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]( vLambda_1(
                                                  try {
                                                    ( {
                                                      vLambda_1: ( Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] => Exception ) =>
                                                        ( {
                                                          vLambda_4: ( Int => ( Tuple2[Int, Unit] => Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] ) ) =>
                                                            ( {
                                                              vLambda_2: ( Tuple2[Int, Unit] => Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] ) =>
                                                                ( {
                                                                  vLambda: Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] => vLambda
                                                                } )( vLambda_2( pair[Int, Unit]( X0 )( vLambda_3 ) ) )
                                                            } )( vLambda_4( f( X0 ) ) )
                                                        } )( ( {
                                                          n: Int =>
                                                            natRec[( Tuple2[Int, Unit] => Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] )]( ( {
                                                              vLambda_6: Tuple2[Int, Unit] =>
                                                                try {
                                                                  ( {
                                                                    vLambda_1: ( Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] => Exception ) =>
                                                                      efq[Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]]( vLambda_5( existsElim[Int, Unit, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]( vLambda_6 )( ( {
                                                                        v_5: Int =>
                                                                          ( {
                                                                            vLambda_14: Unit =>
                                                                              pair[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]( ( {
                                                                                vLambda_7: Tuple2[Int, Unit] =>
                                                                                  existsElim[Int, Unit, Exception]( vLambda_7 )( ( {
                                                                                    v_4: Int =>
                                                                                      ( {
                                                                                        vLambda_9: Unit =>
                                                                                          ( {
                                                                                            vLambda_8: ( Tuple2[Int, Unit] => Exception ) => vLambda_8( pair[Int, Unit]( v_4 )( vLambda_9 ) )
                                                                                          } )( vLambda_10( ( {
                                                                                            vLambda_11: Unit => vLambda_11
                                                                                          } )( vLambda_12( vLambda_13 ) ) ) )
                                                                                      } )
                                                                                  } ) )
                                                                              } ) )( pair[Int, Unit]( v_5 )( vLambda_14 ) )
                                                                          } )
                                                                      } ) ) ) )
                                                                  } )( exception[Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]]( _ )( Some( 3 ) ) )
                                                                } catch {
                                                                  case Exn( v: Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]], Some( id ) ) if id == 3 => {
                                                                    println( "thrown at " + id + " caught at 3" )
                                                                    ( {
                                                                      vLambda: Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] => vLambda
                                                                    } )( v )
                                                                  }
                                                                  case e @ Exn( v, Some( id ) ) => {
                                                                    println( s"throwing further at 3: $v, $id" )
                                                                    throw e
                                                                  }
                                                                }
                                                            } ) )( ( {
                                                              v_0: Int =>
                                                                ( {
                                                                  vLambda_21: ( Tuple2[Int, Unit] => Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] ) =>
                                                                    try {
                                                                      println( "in try 4" )
                                                                      ( {
                                                                        vLambda_17: ( ( Tuple2[Int, Unit] => Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] ) => Exception ) =>
                                                                          println( "in try 4 2" )
                                                                          efq[( Tuple2[Int, Unit] => Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] )]( vLambda_1( pair[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]( s( v_0 ) )(
                                                                            try {
                                                                              println( "in try 5" )
                                                                              ( {
                                                                                vLambda_19: ( Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]] => Exception ) =>
                                                                                  println( "in try 5 2" )
                                                                                  efq[Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]( vLambda_17( ( {
                                                                                    vLambda_18: Tuple2[Int, Unit] =>
                                                                                      existsElim[Int, Unit, Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]]( vLambda_18 )( ( {
                                                                                        v_6: Int =>
                                                                                          ( {
                                                                                            vLambda_27: Unit =>
                                                                                              try {
                                                                                                println( "in try 6" )
                                                                                                val res6 = ( {
                                                                                                  vLambda_1: ( Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] => Exception ) =>
                                                                                                    println( "in try 6 2" )
                                                                                                    efq[Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]]( vLambda_19( pair[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]( ( {
                                                                                                      vLambda_20: Tuple2[Int, Unit] =>
                                                                                                        vLambda_1( existsElim[Int, Unit, Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]]( vLambda_20 )( ( {
                                                                                                          v_7: Int =>
                                                                                                            ( {
                                                                                                              vLambda_24: Unit =>
                                                                                                                ( {
                                                                                                                  vLambda_25: ( Int => ( Unit => Unit ) ) =>
                                                                                                                    ( {
                                                                                                                      vLambda_23: ( Unit => Unit ) =>
                                                                                                                        ( {
                                                                                                                          vLambda_22: Unit =>
                                                                                                                            ( {
                                                                                                                              vLambda: Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] => vLambda
                                                                                                                            } )( vLambda_21( pair[Int, Unit]( v_7 )( vLambda_22 ) ) )
                                                                                                                        } )( vLambda_23( vLambda_24 ) )
                                                                                                                    } )( vLambda_25( v_0 ) )
                                                                                                                } )( vLambda_26( f( v_7 ) ) )
                                                                                                            } )
                                                                                                        } ) ) )
                                                                                                    } ) )( pair[Int, Unit]( v_6 )( vLambda_27 ) ) ) )
                                                                                                } )( exception[Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]]( _ )( Some( 6 ) ) )
                                                                                                println( s"res6: $res6" )
                                                                                                res6
                                                                                              } catch {
                                                                                                case Exn( v: Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]], Some( id ) ) if id == 6 => {
                                                                                                  println( "thrown at " + id + " caught at 6" )
                                                                                                  ( {
                                                                                                    vLambda: Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] => vLambda
                                                                                                  } )( v )
                                                                                                }
                                                                                                case e @ Exn( v, Some( id ) ) => {
                                                                                                  println( s"throwing further at 6: $v, $id" )
                                                                                                  throw e
                                                                                                }
                                                                                              }
                                                                                          } )
                                                                                      } ) )
                                                                                  } ) ) )
                                                                              } )( exception[Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]( _ )( Some( 5 ) ) )
                                                                            } catch {
                                                                              case Exn( v: Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]], Some( id ) ) if id == 5 => {
                                                                                println( "thrown at " + id + " caught at 5" )
                                                                                ( {
                                                                                  vLambda_16: Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]] => vLambda_16
                                                                                } )( v )
                                                                              }
                                                                              case e @ Exn( v, Some( id ) ) => {
                                                                                println( s"throwing further at 5: $v, $id" )
                                                                                throw e
                                                                              }
                                                                              case e => {
                                                                                println( "throwing further at 5" )
                                                                                throw e
                                                                              }
                                                                            } ) ) )
                                                                      } )( exception[( Tuple2[Int, Unit] => Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] )]( _ )( Some( 4 ) ) )
                                                                    } catch {
                                                                      case Exn( v: ( Tuple2[Int, Unit] => Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] ), Some( id ) ) if id == 4 => {
                                                                        println( "thrown at " + id + " caught at 4" )
                                                                        ( {
                                                                          vLambda_15: ( Tuple2[Int, Unit] => Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] ) => vLambda_15
                                                                        } )( v )
                                                                      }
                                                                      case e @ Exn( v, Some( id ) ) => {
                                                                        println( s"throwing further at 4: $v, $id" )
                                                                        throw e
                                                                      }
                                                                    }
                                                                } )
                                                            } ) )( n )
                                                        } ) )
                                                    } )( exception[Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]]( _ )( Some( 2 ) ) )
                                                  } catch {
                                                    case Exn( v: Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]], Some( id ) ) if id == 2 => {
                                                      println( "thrown at " + id + " caught at 2" )
                                                      ( {
                                                        vLambda: Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] => vLambda
                                                      } )( v )
                                                    }
                                                    case e @ Exn( v, Some( id ) ) => {
                                                      println( s"throwing further at 2: $v, $id" )
                                                      throw e
                                                    }
                                                  } ) )
                                            } )( exception[Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]( _ )( Some( 1 ) ) )
                                          } catch {
                                            case Exn( v: Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]], Some( id ) ) if id == 1 => {
                                              println( "thrown at " + id + " caught at 1" )
                                              ( {
                                                vLambda_0: Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]] => vLambda_0
                                              } )( v )
                                            }
                                            case e @ Exn( v, Some( id ) ) => {
                                              println( s"throwing further at 1: $v, $id" )
                                              throw e
                                            }
                                          } )
                                    } )( exception[Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]]( _ )( Some( 0 ) ) )
                                  } catch {
                                    case Exn( v: Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]], Some( id ) ) if id == 0 => {
                                      println( "thrown at " + id + " caught at 0" )
                                      ( {
                                        vLambda: Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] => vLambda
                                      } )( v )
                                    }
                                    case e @ Exn( v, Some( id ) ) => {
                                      println( s"throwing further at 0: $v, $id" )
                                      throw e
                                    }
                                  }
                              } )( vLambda_28( 0 ) )
                          } )( vLambda_29( f( X0 ) ) )
                      } )( vLambda_29( 0 ) )
                  } )( vLambda_30( 0 ) )
              } )
          } )
      } )
  } )

  /*
( {
  vLambda_10: Unit =>
    ( {
      vLambda_6: ( Int => ( Int => ( Unit => Unit ) ) ) =>
        ( {
          vLambda_3: ( Int => Unit ) =>
            ( {
              vLambda_1: ( Int => ( Unit => Unit ) ) =>
                ( {
                  vLambda_0: ( Int => ( Unit => ( Tuple2[Int, Unit] => Exception ) ) ) =>
                    ( {
                      n: Int =>
                        val retNatRec = natRec[( Tuple2[Int, Unit] => Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] )]( ( {
                          vLambda: Tuple2[Int, Unit] =>
                            println( "before existsElim 1" )
                            val ret = existsElim[Int, Unit, Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]]( vLambda )( ( {
                              z: Int =>
                                ( {
                                  vLambda_2: Unit =>
                                    pair[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]( f( z ) )( pair[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]( {
                                      val ftmp = vLambda_0( f( z ) ); println( "ftmp" ); ftmp( vLambda_1( f( z ) )( vLambda_2 ) )
                                    } )( pair[Int, Unit]( z )( vLambda_3( f( z ) ) ) ) )
                                } )
                            } ) )
                            println( "after existsElim 1" )
                            ret
                        } ) )( ( {
                          n: Int =>
                            ( {
                              vLambda_5: ( Tuple2[Int, Unit] => Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]] ) =>
                                ( {
                                  vLambda_9: Tuple2[Int, Unit] =>
                                    try {
                                      println( "in try" )
                                      ( {
                                        vLambda_8: ( Tuple2[Int, Unit] => Exception ) =>
                                          pair[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]( s( n ) )( pair[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]( vLambda_8 )( {
                                            println( s"consuming vLambda_9: $vLambda_9" ); vLambda_9
                                          } ) )
                                      } )( exception[Tuple2[Int, Unit]]( _ )( Some( 0 ) ) )
                                      //throw tmp._2._1( vLambda_9 )
                                    } catch {
                                      case Exn( v: Tuple2[Int, Unit], Some( id ) ) if id == 0 => {
                                        println( s"thrown at $id caught at 0: $v" )
                                        ( {
                                          vLambda_4: Tuple2[Int, Unit] =>
                                            existsElim[Int, Unit, Tuple2[Int, Tuple2[( Tuple2[Int, Unit] => Exception ), Tuple2[Int, Unit]]]]( vLambda_4 )( ( {
                                              x: Int =>
                                                ( {
                                                  vLambda_7: Unit => vLambda_5( pair[Int, Unit]( x )( vLambda_6( f( x ) )( n )( vLambda_7 ) ) )
                                                } )
                                            } ) )
                                        } )( v )
                                      }
                                      case e => {
                                        println( "throwing further at 0" )
                                        throw e
                                      }
                                    }
                                } )
                            } )
                        } ) )( n )
                        println( "after natRec" )
                        retNatRec
                    } )( f( 0 ) )( pair[Int, Unit]( 0 )( vLambda_10 ) )
                } )
            } )
        } )
    } )
} )
*/

  val arg1 = {
    _: Int =>
      {
        _: Int =>
          {
            _: Unit =>
              {
                ()
              }
          }
      }
  }
  val arg2 = {
    _: Int =>
      {
        ()
      }
  }
  val arg3 = {
    _: Int =>
      {
        _: Unit =>
          {
            ()
          }
      }
  }
  //val lem3 = hof"!x (x = 0 -> -(?y f(y) < x))"
  val arg4 = {
    x: Int =>
      {
        y: Unit =>
          {
            arg: Tuple2[Int, Unit] =>
              {
                println( "in arg4" )
                exception( arg )( None )
              }
          }
      }
  }
  //val realHasminProgram = hasminProgram()( arg1 )( arg2 )( arg3 )( arg4 )
  val realHasminProgram = hasminProgram( arg3 )( arg4 )( arg1 )( arg2 )
  val res = realHasminProgram
  println( s"res: $res" )
  val min = res._1
  //val min = 0
  if ( !( 0 to 1000 forall ( x => f( x ) >= min ) ) ) {
    println( s"minimum ${min} incorrect" )
    assert( false )
  } else {
    println( s"minimum ${min} correct" )
  }

}

object exceptionTest extends Script {
  case class Exn[A]( v: A, id: Option[Int] ) extends Exception
  def f =
    try {
      try {
        throw Exn( 5, Some( 5 ) )
      } catch {
        case Exn( _, id ) if id == 6 =>
          println( s"caught $id" )
        case e @ Exn( _, id ) =>
          println( s"throwing further at 6" )
          throw e
      }
    } catch {
      case Exn( _, id ) if id == 5 =>
        println( s"caught $id" )
      case e @ Exn( _, id ) =>
        println( s"throwing further at 5" )
        throw e
    }

  try {
    f
  } catch {
    case Exn( _, id ) if id == 2 =>
      println( s"caught $id" )
    case e @ Exn( _, id ) =>
      println( s"throwing further at 2" )
      throw e
  }

}

object permutationRules extends Script {

  def s( x: Int ) = x + 1

  def leq( x: Int )( y: Int ) = x <= y

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
      println( "base case" )
      p1
    } else {
      println( "step case" )
      p2( p3 - 1 )( natRec( p1 )( p2 )( p3 - 1 ) )
    }
  }

  case class Exn[A]( v: A, id: Option[Int] ) extends Exception

  def exception[A]( v: A )( id: Option[Int] = None ) = new Exn( v, id )

  def existsElim[A, B, C]( p1: Tuple2[A, B] )( p2: A => B => C ) = p2( p1._1 )( p1._2 )

  def pi1[A, B]( p: ( A, B ) ) = p._1

  def add( x: Int )( y: Int ) = x + y

  def pair[A, B]( p0: A )( p1: B ): Tuple2[A, B] = ( p0, p1 )

  def efq[B]( p: Throwable ): B = throw p

  def f: ( Int => Int ) =
    try {
      // if throwing an exception in returned function,
      // it won't be caught by catch block
      { case x: Int => x + 3 }
    } catch {
      case _ => { case x: Int => x + 6 }
    }
  println( f( 0 ) )

  def g: Tuple2[Int, String] =
    try {
      ( 3, "catch" )
    } catch {
      case _ => ( 6, "exn" )
    }
  println( pi1( g ) )
  println( pi2( g ) )

  def h: ( Sum[Int, String] ) =
    try {
      // if throwing an exception in returned function,
      // it won't be caught by catch block
      Inl[Int, String]( 3 )
      throw Exn( "exn", Some( 0 ) )
    } catch {
      case Exn( v: String, id ) if id == Some( 0 ) => Inr[Int, String]( v )
      case e                                       => throw e
    }
  println( h match {
    case Inl( x ) => x
    case Inr( y ) => y
  } )

  def i: Tuple2[Int, String] =
    try {
      ( 3, "try" )
    } catch {
      case _ => ( 6, "catch" )
    }
  println( existsElim( i )( { x: Int => { y: String => s"result: $x $y" } } ) )
}

object trycatchTest extends Script {

  import gapt.expr._
  import gapt.formats.babel.{ Notation, Precedence }
  import gapt.proofs.context.Context
  import gapt.proofs.nd._

  implicit var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += Notation.Infix( "<", Precedence.infixRel )
  ctx += hoc"'<': nat>nat>o"
  ctx += hoc"'P': nat>o"

  val constructive = ProofBuilder.
    c( LogicalAxiom( hof"-(?x (P x))" ) ).
    c( LogicalAxiom( hof"P x" ) ).
    u( ExistsIntroRule( _, hof"?x (P x)" ) ).
    b( NegElimRule( _, _ ) ).
    u( NegIntroRule( _, hof"P x" ) ).
    qed
  val classical = ProofBuilder.
    c( LogicalAxiom( hof"-(?x (P x))" ) ).
    c( LogicalAxiom( hof"P x" ) ).
    u( ExistsIntroRule( _, hof"?x (P x)" ) ).
    b( NegElimRule( _, _ ) ).
    u( BottomElimRule( _, hof"-(P x)" ) ).
    c( LogicalAxiom( hof"-(P x)" ) ).
    b( ExcludedMiddleRule( _, _ ) ).
    qed
  /*
val proof = ProofBuilder.
  c( LogicalAxiom( hof"?x (x < 0)" ) ).
  c( LogicalAxiom( hof"-(x < 0)" ) ).
  c( LogicalAxiom( hof"x < 0" ) ).
  b( NegElimRule( _, _ ) ).
  u( ImpIntroRule( _, hof"-(x < 0)" ) ).
  c( LogicalAxiom( hof"(!x -(x < 0))" ) ).
  u( ForallElimRule( _, le"x:nat" ) ).
  b( ImpElimRule( _, _ ) ).
  b( ExistsElimRule( _, _ ) ).
  u( BottomElimRule( _, hof"-(?x (x < 0))" ) ).
  c( LogicalAxiom( hof"-(?x (x < 0))" ) ).
  b( ExcludedMiddleRule( _, _ ) ).
  u( ImpIntroRule( _ ) ).
  qed
    */
  prooftool( constructive )
  val lambdaConstructive = ClassicalExtraction.extractCases( constructive )
  ScalaCodeGenerator( "constructive" )( lambdaConstructive )( ClassicalExtraction.systemT( ctx ) )
  prooftool( classical )
  val lambdaClassical = ClassicalExtraction.extractCases( classical )
  ScalaCodeGenerator( "classical" )( lambdaClassical )( ClassicalExtraction.systemT( ctx ) )
  println( s"constructive type:\n${lambdaConstructive.ty}" )
  println( s"classical type:\n${lambdaClassical.ty}" )
}

object trycatchTestSynth extends Script {

  def s( x: Int ) = x + 1
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
  def existsElim[A, B, C]( p1: Tuple2[A, B] )( p2: A => B => C ) = p2( p1._1 )( p1._2 )
  def raise[A]( x: A ): Exception = throw exception( x )( None ) // TODO get name/id of hypothesis variable in extraction
  def pi1[A, B]( p: ( A, B ) ) = p._1
  def pair[A, B]( p0: A )( p1: B ): Tuple2[A, B] = ( p0, p1 )
  def efq[B]( p: Throwable ): B = throw p
  val prog = ( {
    vLambda_1: ( Int => ( Unit => Exception ) ) =>
      try {
        ( {
          vHyp_0: ( Tuple2[Int, Unit] => Exception ) => vHyp_0
        } )( exception[Tuple2[Int, Unit]]( _ )( Some( 0 ) ) )
      } catch {
        case Exn( v: Tuple2[Int, Unit], Some( id ) ) if id == 0 => {
          //println( "thrown at " + id + " caught at 0" )
          ( {
            vHyp: Tuple2[Int, Unit] =>
              efq[( Tuple2[Int, Unit] => Exception )]( existsElim[Int, Unit, Exception]( vHyp )( ( {
                x: Int =>
                  ( {
                    vLambda_0: Unit =>
                      ( {
                        vLambda: ( Unit => Exception ) => vLambda( vLambda_0 )
                      } )( vLambda_1( x ) )
                  } )
              } ) ) )
          } )( v )
        }
        case e => {
          //println("throwing further at 0")
          throw e
        }
      }
  } )
  prog( { _: Int => { arg: Unit => exception( arg )( None ) } } )

}

/*
object consistencyProblem extends Script {
case class Exn[A]( v: A, id: Option[Int] ) extends Exception
def exception[A]( v: A )( id: Option[Int] = None ) = new Exn( v, id )
def pair = {x: Int => {
  y: Int =>
try {
  {P : (Int => Int => Exception) => P}(exception(_)(None))
} catch {
  case Exn(g: (Int => Int => Exception), _) => throw g(x)(y)
}
}}
pair(1)(2)._1
}
*/

object throwReductionRules extends Script {
  case class Exn[A]( v: A, id: Option[Int] ) extends Exception
  try {
    ( throw Exn( 0, None ) )
    throw Exn( 1, None )
  } catch {
    case Exn( v, _ ) => println( s"case $v" )
  }
  try {
    val v: Exception => Int = ( throw Exn( 0, None ) )
    v( throw Exn( 1, None ) )
  } catch {
    case Exn( v, _ ) => println( s"case $v" )
  }
  try {
    ( { x: Int => x } )( throw Exn( 1, None ) )
  } catch {
    case Exn( v, _ ) => println( s"case $v" )
  }
  try {
    ( { x: Int => throw Exn( 0, None ) } )( throw Exn( 1, None ) )
  } catch {
    case Exn( v, _ ) => println( s"case $v" )
  }
  try {
    throw ( throw Exn( 2, None ) )
  } catch {
    case Exn( v, _ ) => println( s"case $v" )
  }
}

object churchRosserFailure extends Script {
  import gapt.expr._
  import gapt.formats.babel.{ Notation, Precedence }
  import gapt.proofs.context.Context
  import gapt.proofs.nd._

  implicit var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += Notation.Infix( "<", Precedence.infixRel )
  ctx += hoc"'<': nat>nat>o"
  ctx += hoc"'P': nat>o"
  ctx += hoc"'c': nat"
  ctx += hoc"'d': nat"
  ctx += hoc"'e': nat"

  val lemma = ProofBuilder.
    c( LogicalAxiom( hof"P v" ) ).
    c( LogicalAxiom( hof"-(?x (-(P x)))" ) ).
    c( LogicalAxiom( hof"-(P v)" ) ).
    u( ExistsIntroRule( _, hof"?x (-(P x))" ) ).
    b( NegElimRule( _, _ ) ).
    u( BottomElimRule( _, hof"P v" ) ).
    b( ExcludedMiddleRule( _, _ ) ).
    u( ForallIntroRule( _, hof"!x (P x)", hov"v: nat" ) ).
    qed

  val posBranch = ProofBuilder.
    c( LogicalAxiom( hof"?x (-(P x))" ) ).
    c( LogicalAxiom( hof"-(P x)" ) ).
    u( WeakeningRule( _, hof"(P c) -> -(P d)" ) ).
    u( ImpIntroRule( _, hof"(P c) -> -(P d)" ) ).
    u( ExistsIntroRule( _, hof"?x (((P c) -> -(P d)) -> -(P x))" ) ).
    b( ExistsElimRule( _, _ ) ).
    qed

  val negBranch = ProofBuilder.
    c( LogicalAxiom( hof"(P c) -> -(P d)" ) ).
    c( LogicalAxiom( hof"!x (P x)" ) ).
    u( ForallElimRule( _, le"c:nat" ) ).
    u( WeakeningRule( _, hof"P e" ) ).
    u( ImpIntroRule( _, hof"P e" ) ).
    c( LogicalAxiom( hof"!x (P x)" ) ).
    u( ForallElimRule( _, le"e:nat" ) ).
    b( ImpElimRule( _, _ ) ).
    b( ImpElimRule( _, _ ) ).
    u( ImpIntroRule( _, hof"(P c) -> -(P d)" ) ).
    u( ExistsIntroRule( _, hof"?x (((P c) -> -(P d)) -> -(P x))" ) ).
    u( ContractionRule( _, hof"!x (P x)" ) ).
    u( ImpIntroRule( _ ) ).
    c( lemma ).
    b( ImpElimRule( _, _ ) ).
    qed

  val proof = ProofBuilder.
    c( posBranch ).
    c( negBranch ).
    b( ExcludedMiddleRule( _, _ ) ).
    qed

  prooftool( proof )
  val lambda = ClassicalExtraction.extractCases( proof )
  ScalaCodeGenerator( "churchRosserFailureProgram" )( lambda )( ClassicalExtraction.systemT( ctx ) )
  println( s"reduced: ${normalize( lambda )}" )
}

object churchRosserFailureProgram extends Script {

  def s( x: Int ) = x + 1
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
  def existsElim[A, B, C]( p1: Tuple2[A, B] )( p2: A => B => C ) = p2( p1._1 )( p1._2 )
  def raise[A]( x: A ): Exception = throw exception( x )( None ) // TODO get name/id of hypothesis variable in extraction
  def pi1[A, B]( p: ( A, B ) ) = p._1
  def pair[A, B]( p0: A )( p1: B ): Tuple2[A, B] = ( p0, p1 )
  def efq[B]( p: Throwable ): B = throw p

  val c = 0
  val d = 1
  val e = 2

  val prog: ( Int, ( Unit => Unit => Exception ) => Unit => Exception ) = try {
    ( {
      vLambda_5: ( Tuple2[Int, ( Unit => Exception )] => Exception ) =>
        ( {
          vLambda_2: ( Int => Unit ) =>
            pair[Int, ( ( Unit => ( Unit => Exception ) ) => ( Unit => Exception ) )]( d )( ( {
              vLambda_1: ( Unit => ( Unit => Exception ) ) =>
                vLambda_1( ( {
                  vLambda_3: Unit => vLambda_2( c )
                } )( vLambda_2( e ) ) )
            } ) )
        } )( ( {
          v: Int =>
            try {
              ( {
                vLambda_6: ( Unit => Exception ) => efq[Unit]( vLambda_5( pair[Int, ( Unit => Exception )]( v )( vLambda_6 ) ) )
              } )( exception[Unit]( _ )( Some( 1 ) ) )
            } catch {
              case Exn( v: Unit, Some( id ) ) if id == 1 => {
                //println( "thrown at " + id + " caught at 1" )
                ( {
                  vLambda_4: Unit => vLambda_4
                } )( v )
              }
              case e => {
                //println("throwing further at 1")
                throw e
              }
            }
        } ) )
    } )( exception[Tuple2[Int, ( Unit => Exception )]]( _ )( Some( 0 ) ) )
  } catch {
    case Exn( v: Tuple2[Int, ( Unit => Exception )], Some( id ) ) if id == 0 => {
      //println( "thrown at " + id + " caught at 0" )
      ( {
        vLambda: Tuple2[Int, ( Unit => Exception )] =>
          existsElim[Int, ( Unit => Exception ), Tuple2[Int, ( ( Unit => ( Unit => Exception ) ) => ( Unit => Exception ) )]]( vLambda )( ( {
            x: Int =>
              ( {
                vLambda_0: ( Unit => Exception ) =>
                  pair[Int, ( ( Unit => ( Unit => Exception ) ) => ( Unit => Exception ) )]( x )( ( {
                    vLambda_1: ( Unit => ( Unit => Exception ) ) => vLambda_0
                  } ) )
              } )
          } ) )
      } )( v )
    }
    case e => {
      //println("throwing further at 0")
      throw e
    }
  }
  println( s"prog: $prog" )

}

object reductionExamples extends Script {
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )

  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )

  val y = le"(^x x)0"
  println( y )
  ctxClassical += hoc"c{?a ?b}:?a>?b"

  println( normalize( le"efq(exception(0))($y)" ) )
  ctxClassical += ReductionRuleUpdate( "efq(x)(y) = efq(x)" )
  println( "after adding reduction rule:" )
  assert( normalize( le"efq(exception(0))($y)" ) == le"efq(exception(0))" )

  println( normalize( le"(^x y)(efq(exception(0)))" ) )
  //ctxClassical += ReductionRuleUpdate( "(c)(efq(x)) = efq(x)" )
  println( "after adding reduction rule:" )
  println( normalize( le"(^x y)(efq(exception(0)))" ) )
  assert( normalize( le"(^x y)(efq(exception(0)))" ) == le"efq(exception(0))" )

  println( normalize( le"s(efq(efq(exception($y))))" ) )
  //ctxClassical += ReductionRuleUpdate( "efq(efq(x)) = efq(x)" )
  println( "after adding reduction rule:" )
  println( normalize( le"s(efq(efq(exception(0))))" ) )
  println( le"efq(exception(0))" )
  // TODO normalizes to inner-most efq, which has wrong type
  assert( normalize( le"s(efq(efq(exception(0))))" ) == le"efq(exception(0))" )

  val f = le"(^x efq(exception(z)))"
  //val tryCatch = hoc"tryCatch{?a ?c}: (?a > ?c) > ((?a > (exn ?a)) > ?c) > ?c"
  //val handle = hoc"handle{?a ?c}: (exn ?a) > (?a > ?c) > ?c"
  val x = le"x:nat"
  println( normalize( le"tryCatch(handle(exception($x), (^y v)))((^z efq(z(0)))(exception))" ) )

  // TODO only if z not in FV of w
  ctxClassical += ReductionRuleUpdate( "tryCatch(handle(exception(x), (^y v)))((^z w)) = w" )
  ctxClassical += ReductionRuleUpdate( "tryCatch(handle(exception(x), (^x v)))((^z efq(z(w)))) = v(w)" )

  //ctxClassical += ReductionRuleUpdate( "tryCatch(handle(exception(x), (^y v)))((^z efq(z(0)))) = v(0)" )
  println( normalize( le"tryCatch(handle(exception($x), (^x(^(v:nat) v))))((^z efq(z(0))))" ) )
  println( normalize( le"tryCatch(handle(exception($x), (^x(^(v:nat) (^w v)))))((^z efq(z(0)))exception)$y" ) )

  //println( normalize( le"tryCatch(handle(exception($x), (^z z)))((^z efq(z(0)))(exception))$y" ) )
  ctxClassical += ReductionRuleUpdate( "tryCatch(^x U)(^y V)W = em(^x (U(W)))(^y (V(W)))" )
  println( "after adding reduction rule:" )
  println( normalize( le"tryCatch((^z z))((^z efq(z(0)))(exception))$y" ) )
}

object commutingConversions extends Script {
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += Notation.Infix( "+", Precedence.plusMinus )
  ctx += hoc"'+': nat>nat>nat"

  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )

  val tryCatch = le"tryCatch((^y0 (M0:?a_0)), handle(y0(x0:?a_0), (N0:?a_0)))"
  val tryCatch2 = le"tryCatch((^y1 (^(z:?a_0) M1)), handle(y1(x1), (^(z:?a_0) N1)))"
  val tryCatch3 = le"tryCatch((^y1 (M1: ?a_0 > ?a_1)), handle(y1(x1), (N1: ?a_0 > ?a_1)))"
  val tryCatch4 = le"tryCatch((^y0 (M0: exn ?a)), handle(y0(x0), (N0: exn ?a)))"
  val tryCatch5 = le"tryCatch((^y2 (M2: (?a_0 > ?a_1) > ?a_0 > ?a_2)), handle(y2(x2), (N2: (?a_0 > ?a_1) > ?a_0 > ?a_2)))"
  val tryCatch6 = le"tryCatch((^y0 efq(y0(M0:?a_0))), handle(y0(x0), (N0:?a_0)))"
  val tryCatch7 = le"tryCatch((^y1 (efq(y1(M1:?a_0)): ?a_0 > ?a_1)), handle(y1(x1:?a_0), (N1: ?a_0 > ?a_1)))"
  val efq = le"efq(exception(0))(M:?a_0)"
  val efq2 = le"efq(efq(exception(0)))(M:?a_0)"
  val efq3 = le"efq(exception(0))(efq(exception(1)))"

  val tryCatch8 = le"""
tryCatch(
  (^y1
    (efq(y1(0:nat)): nat > nat)),
  handle(y1(x1:nat),
    (^(z:nat) s(z)))
  )(tryCatch(
      (^y0
        s(x1)),
      handle(y0(x0:nat),
        (x0 + x1))
  )
)"""
  val tryCatch9 = le"""
tryCatch(
  (^y1
    (efq(y1(0:nat)): nat > nat)),
  handle(y1(x1:nat),
    (^(z:nat) s(z)))
  )(tryCatch(
      (^y0
        efq(y0(s(x1))): nat),
      handle(y0(x0:nat),
        (x0 + x1))
  )
)"""
  val tryCatch10 = le"""
tryCatch(
  (^y1
    (^z efq(y1(z)): nat)),
  handle(y1(x1:nat),
    (^(w:nat) s(w)))
)(0)"""

  /*
  println( tryCatch )
  println( tryCatch2 )
  println( "1:" + normalize( le"V($tryCatch)" ) )
  */
  // TODO: Can't be implemented via a reduction rule update
  // ctxClassical += ReductionRuleUpdate( "V(em(handle(y(x), N), (^y M))) = em(handle(y(x), V(N)), (^y V(M)))" )
  /*
  println( "2:" + normalize( le"($tryCatch2)(O)" ) )
  println( "3:" + normalize( le"($tryCatch2)($tryCatch)" ) )
  println( "4:" + normalize( le"($tryCatch3)(O)" ) )
  println( "6:" + normalize( le"V($tryCatch3)(O)" ) )
  println( "7:" + normalize( le"((^x x)V)($tryCatch3)((^y y)O)" ) )
  println( "8:" + normalize( le"efq($tryCatch4)" ) )
  println( "5:" + normalize( le"($tryCatch3)($tryCatch)" ) )
  println( "9:" + normalize( le"($tryCatch5)($tryCatch3)($tryCatch)" ) )
  println( "10:" + normalize( le"($tryCatch6)" ) )
  println( "11:" + normalize( le"($efq)" ) )
  println( "12:" + normalize( le"($efq2)" ) )
  println( "13:" + normalize( le"($efq3)" ) )
  println( "14:" + normalize( le"($tryCatch7)($tryCatch)" ) )
  println( "15:" + normalize( le"$tryCatch8" ) )
  println( "16:" + normalize( le"$tryCatch9" ) )
  println( "17:" + normalize( le"$tryCatch10" ) )
  */
  /*
  normalize(
    le"""
s(tryCatch(
  (^(y1: nat>exn) 0),
  handle(y1(x1:nat),
    s(0))
))""" )
*/

  val pair =
    le"""
       (^(x: nat) ^(y: nat)
         (^(f: nat>nat>exn)
           (f x y)
         )
       )"""
  val proj1 =
    le"""
       (^(p: (nat>nat>exn)>exn)
         tryCatch(
          (^(y:nat>exn)
            efq(p(^(x:nat) efq(y(x))))
          ),
          handle(y(x:nat), x)
         )
       )
      """
  val proj2 =
    le"""
       (^(p: (nat>nat>exn)>exn)
         tryCatch(
          (^(y:nat>exn)
            efq(p(^(x:nat) y))
          ),
          handle(y(x:nat), x)
         )
       )
      """
  val classicalPairing = proj2( pair( hoc"0:nat", le"s(0):nat" ) )
  println( normalize( classicalPairing ) )
}

object commutingConversions2 extends Script {
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )

  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )

  //println( normalize( le"efq(tryCatch((^(y0: nat>exn) y0(0)), handle((y0: nat>exn)(x0:nat), (N0: nat>exn)(x0)))): nat" ) )
  //println( normalize( le"efq(f(tryCatch((^(y0: nat>exn) y0(0)), handle((y0: nat>exn)(x0:nat), (N0: nat>exn)(x0))))): nat" ) )
  println( normalize( le"""
    efq(f(
      (^(y0: nat>exn) tryCatch(y0,
                        y0(0),
                        handle((y0: nat>exn)(x0:nat), (N0: nat>exn)(x0))
                      ))(exnV))): nat""" ) )

  /*
  println( normalize(
    le"""
         existsElim(
           tryCatch(
             (^(y0: nat>exn) pair(y0, i)),
             handle((y0:nat>exn)(x0:nat), (N0:conj(nat>exn)(1)))
           ), (^(x:nat>exn) (^(y:1) x(0)))
         )
      """ ) )
  println( normalize(
    le"""
         existsElim(
           tryCatch(
             (^(y0: nat>exn) pair(y0, i)),
             handle((y0:nat>exn)(x0:nat), (N0:conj(nat>exn)(1)))
           ), (^(x:nat>exn) (^(y:1) efq(x(0))))
         )
      """ ) )
      */
}

object handleRaiseReduction extends Script {
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )

  // reduces to N0(0) or N1(0) depending on which exception variable is raised
  println( normalize(
    le"""
        tryCatch(
          (^(y0: nat>exn)
            tryCatch(
              (^(y1: nat>exn)
                efq(y0(0)):nat),
            handle(
              (y1: nat>exn)(x0: nat), (N1: nat>nat)(x0))
            )),
        handle(
          (y0: nat>exn)(x0:nat), (N0: nat>nat)(x0))
        ): nat""" ) )
}

object testExistsElimTryCatch extends Script {
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  /*
  println( normalize( le"""
       existsElim(
         pair(0, i:1),
         (^(v1: nat) (^(v2: 1)
               pair(v1, v2)
         ) )
       )
    """ ) )
  println( normalize( le"""
       existsElim(
         pair(0, i:1),
         (^(v1: nat) (^(v2: 1)
           tryCatch(
             (^(vLambda_13: (conj(nat)(1))>exn)
               (efq(vLambda_13(pair(v1, v2))):conj(nat)(1))),
               handle(
                 (vLambda_13: (conj(nat)(1))>exn)(x: conj(nat)(1)), x
               )
           )
         ) )
       )
    """ ) )
    */
  println( normalize( le"""
       natRec(
         base: conj(nat)(1),
         (^(r:nat)(^(p:conj(nat)(1))
         existsElim(
           pair(r, i:1),
           (^(v1: nat) (^(v2: 1)
             (^(vLambda_13: (conj(nat)(1))>exn) tryCatch(vLambda_13,
                 (efq(vLambda_13(pair(v1, v2))):conj(nat)(1)),
                 handle(
                   (vLambda_13: (conj(nat)(1))>exn)(x: conj(nat)(1)), x
                 )
             ))(exnV)
           ) )
         ))),
         s(0))
    """ ) )
  println( normalize( le"(^x (^x s(x)))(0)(1)" ) )
}

object handleSimp extends Script {
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  val f = normalize // ScalaCodeGenerator
  println( f( le"""
s((^(y1: nat>exn) tryCatch(y1,
   0,
  handle(y1(x1:nat),
    s(0)))
)(exnV))""" ) )
}
object handleRaise extends Script {
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  val f = normalize // ScalaCodeGenerator
  println( f( le"""
s((^(y1: nat>exn)
    tryCatch(y1,
    (^(y2: nat>exn)
      tryCatch(y2,
        efq(y1(0)),
      handle(y2(x1:nat),
        s(x1))))(exnV1),
  handle(y1(x1:nat),
    x1))
)(exnV))""" ) )
}
object exceptionCarryingException extends Script {
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  val f = normalize // ScalaCodeGenerator
  println( f( le"""
s((^(y1: (nat>exn)>exn)
    tryCatch(y1,
    (^(y2: nat>exn)
      tryCatch(y2,
        efq(y1(y2)),
      handle(y2(x1:nat),
        s(x1))))(exnV1),
  handle(y1(x2:nat>exn),
    efq(x2(0))))
)(exnV))""" ) )
}

object reduceMatchSum extends Script {
  import gapt.proofs.context.Context
  import gapt.proofs.nd.ClassicalExtraction
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  println( normalize( le"""
         matchSum(
           (^(y0: nat>exn) tryCatch(y0,
             inr(y0(0)): sum(nat)(exn),
             handle(
               y0(x0:nat), inl(x0): sum(nat)(exn)
             ))
           )(myExn:nat>exn))(
           ^(c1: nat) s(0)
           )(
           ^(c2: exn) efq(c2)
           )
  """ ) )
}
object commuteEfqInfiniteExecution extends Script {
  import gapt.proofs.context.Context
  import gapt.proofs.nd.ClassicalExtraction
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  println( normalize( le"""
         efq(matchSum(
          (^(y0: nat>exn) tryCatch(y0,
            inl(y0): sum(nat>exn)(exn),
            handle(
              y0(x0:nat), inr(y0(x0)): sum(nat>exn)(exn)
            ))
          )(myExn:nat>exn))(
          ^(c1: nat>exn) c1(0)
          )(
          ^(c2: exn) c2
          ))
  """ ) )
}

object booleanDeterminization extends Script {
  import gapt.proofs.context.Context
  import gapt.proofs.nd.ClassicalExtraction
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  val p = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"x" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"x" ) ).
    b( AndIntroRule( _, _ ) ).
    u( OrIntro2Rule( _, hof"-x & x" ) ).
    u( ExistsIntroRule( _, hof"?y ((-x & y) | (x & y))" ) ).
    u( ContractionRule( _, hof"x" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"-x" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"-x" ) ).
    b( AndIntroRule( _, _ ) ).
    u( OrIntro1Rule( _, hof"x & -x" ) ).
    u( ExistsIntroRule( _, hof"?y ((-x & y) | (x & y))" ) ).
    u( ContractionRule( _, hof"-x" ) ).
    b( ExcludedMiddleRule( _, _ ) ).
    u( ForallIntroRule( _, hof"!(x:o)?y ((-x & y) | (x & y))", hov"x:o" ) ).
    qed
  println( p )
  prooftool( p )
  val lam = ClassicalExtraction.extractCases( p )
  println( lam )
}

object bugFirstOrderType extends Script {
  import gapt.proofs.context.Context
  import gapt.proofs.nd.ClassicalExtraction
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  val p = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"-x" ) ).
    u( ExistsIntroRule( _, hof"?y y" ) ).
    qed
  println( p )
  val lam = ClassicalExtraction.extractCases( p )
  println( lam )
}

object booleanDeterminization2 extends Script {
  import gapt.proofs.context.Context
  import gapt.proofs.nd.ClassicalExtraction
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  val p1 = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"-x" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"-x" ) ).
    b( AndIntroRule( _, _ ) ).
    u( ContractionRule( _, hof"-x" ) ).
    u( OrIntro1Rule( _, hof"-x & -(-x)" ) ).
    u( OrIntro1Rule( _, hof"x & -x" ) ).
    u( ExistsIntroRule( _, hof"?y (((-x & y) | (-x & -y)) | (x & y))" ) ).
    qed
  println( p1 )
  val p2 = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"-x" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"-(-x)" ) ).
    b( AndIntroRule( _, _ ) ).
    u( OrIntro2Rule( _, hof"-x & -x" ) ).
    u( OrIntro1Rule( _, hof"x & -x" ) ).
    u( ExistsIntroRule( _, hof"?y (((-x & y) | (-x & -y)) | (x & y))" ) ).
    qed
  println( p2 )
  val p3 = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"x" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"x" ) ).
    b( AndIntroRule( _, _ ) ).
    u( ContractionRule( _, hof"x" ) ).
    u( OrIntro2Rule( _, hof"-x & x | -x & -x" ) ).
    u( ExistsIntroRule( _, hof"?y (((-x & y) | (-x & -y)) | (x & y))" ) ).
    qed
  println( p3 )
  val p = ProofBuilder.
    c( p3 ).
    c( p1 ).
    c( p2 ).
    b( ExcludedMiddleRule( _, _ ) ).
    b( ExcludedMiddleRule( _, _ ) ).
    u( ForallIntroRule( _, hof"!(x:o)?y (((-x & y) | (-x & -y)) | (x & y))", hov"x:o" ) ).
    qed
  println( p )
  prooftool( p )
  val lam = ClassicalExtraction.extractCases( p )
  println(lam)
}

object booleanDeterminization3 extends Script {
  import gapt.proofs.context.Context
  import gapt.proofs.nd.ClassicalExtraction
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += InductiveType( "bool", hoc"bFalse: bool", hoc"bTrue: bool" )
  val Some( bFalse ) = ctx.constant( "bFalse" )
  val Some( bTrue ) = ctx.constant( "bTrue" )
  val bIsTrue = hoc"p : bool>o"
  ctx += PrimitiveRecursiveFunction(
    bIsTrue,
    List(
      ( bIsTrue( bFalse ) -> hof"false" ),
      ( bIsTrue( bTrue ) -> hof"true" ) ) )( ctx )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  val p1 = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"-p(x)" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"p(x)" ) ).
    b( AndIntroRule( _, _ ) ).
    u( OrIntro1Rule( _, hof"-p(x) & -p(x)" ) ).
    u( OrIntro1Rule( _, hof"p(x) & p(x)" ) ).
    u( ExistsIntroRule( _, hof"?y (((-p(x) & p(y)) | (-p(x) & -p(y))) | (p(x) & p(y)))" ) ).
    qed
  println( p1 )
  val p2 = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"-p(x)" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"-p(x)" ) ).
    b( AndIntroRule( _, _ ) ).
    u( ContractionRule( _, hof"-p(x)" ) ).
    u( OrIntro2Rule( _, hof"-p(x) & p(x)" ) ).
    u( OrIntro1Rule( _, hof"p(x) & p(x)" ) ).
    u( ExistsIntroRule( _, hof"?y (((-p(x) & p(y)) | (-p(x) & -p(y))) | (p(x) & p(y)))" ) ).
    qed
  println( p2 )
  val p3 = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"p(x)" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"p(x)" ) ).
    b( AndIntroRule( _, _ ) ).
    u( ContractionRule( _, hof"p(x)" ) ).
    u( OrIntro2Rule( _, hof"-p(x) & p(x) | -p(x) & -p(x)" ) ).
    u( ExistsIntroRule( _, hof"?y (((-p(x) & p(y)) | (-p(x) & -p(y))) | (p(x) & p(y)))" ) ).
    qed
  println( p3 )
  val p = ProofBuilder.
    c( p3 ).
    c( p1 ).
    c( p2 ).
    b( ExcludedMiddleRule( _, _ ) ).
    b( ExcludedMiddleRule( _, _ ) ).
    u( ForallIntroRule( _, hof"!(x:bool)?y (((-p(x) & p(y)) | (-p(x) & -p(y))) | (p(x) & p(y)))", hov"x:bool" ) ).
    qed
  println( p )
  prooftool( p )
  val lam = ClassicalExtraction.extractCases( p )
  println( lam.toUntypedString )
  println( normalize( lam( bTrue ) ).toUntypedString )
  /*
  println(normalize(lam(bFalse)))
  */
}

object booleanDeterminization4 extends Script {
  import gapt.proofs.context.Context
  import gapt.proofs.nd.ClassicalExtraction
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  val p1 = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"-x" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"x" ) ).
    b( AndIntroRule( _, _ ) ).
    u( OrIntro1Rule( _, hof"-x & -x" ) ).
    u( OrIntro1Rule( _, hof"x & x" ) ).
    u( ExistsIntroRule( _, hof"?y (((-x & y) | (-x & -y)) | (x & y))" ) ).
    qed
  println( p1 )
  val p2 = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"-x" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"-x" ) ).
    b( AndIntroRule( _, _ ) ).
    u( ContractionRule( _, hof"-x" ) ).
    u( OrIntro2Rule( _, hof"-x & x" ) ).
    u( OrIntro1Rule( _, hof"x & x" ) ).
    u( ExistsIntroRule( _, hof"?y (((-x & y) | (-x & -y)) | (x & y))" ) ).
    qed
  println( p2 )
  val p3 = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"x" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"x" ) ).
    b( AndIntroRule( _, _ ) ).
    u( ContractionRule( _, hof"x" ) ).
    u( OrIntro2Rule( _, hof"-x & x | -x & -x" ) ).
    u( ExistsIntroRule( _, hof"?y (((-x & y) | (-x & -y)) | (x & y))" ) ).
    qed
  println( p3 )
  val p = ProofBuilder.
    c( p3 ).
    c( p1 ).
    c( p2 ).
    b( ExcludedMiddleRule( _, _ ) ).
    b( ExcludedMiddleRule( _, _ ) ).
    u( ForallIntroRule( _, hof"!(x:o)?y (((-x & y) | (-x & -y)) | (x & y))", hov"x:o" ) ).
    qed
  println( p )
  prooftool( p )
  val lam = ClassicalExtraction.extractCases( p )
  println( lam.toUntypedAsciiString )
  /*
  println(normalize(lam(bTrue)))
  println(normalize(lam(bFalse)))
  */
}

object booleanDetTwoVars extends Script {
  import gapt.proofs.context.Context
  import gapt.proofs.nd.ClassicalExtraction
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += InductiveType( "bool", hoc"bFalse: bool", hoc"bTrue: bool" )
  val Some( bFalse ) = ctx.constant( "bFalse" )
  val Some( bTrue ) = ctx.constant( "bTrue" )
  val bIsTrue = hoc"p : bool>o"
  ctx += PrimitiveRecursiveFunction(
    bIsTrue,
    List(
      ( bIsTrue( bFalse ) -> hof"false" ),
      ( bIsTrue( bTrue ) -> hof"true" ) ) )( ctx )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  val p1 = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"-p(x1)" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"-p(x2)" ) ).
    b( AndIntroRule( _, _ ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"-p(x1)" ) ).
    b( AndIntroRule( _, _ ) ).
    u( ContractionRule( _, hof"-p(x1)" ) ).
    u( OrIntro1Rule( _, hof"-p(x1) & p(x2) & p(x1)" ) ).
    u( OrIntro1Rule( _, hof"p(x1) & -p(x2) & p(x1)" ) ).
    u( OrIntro1Rule( _, hof"p(x1) & p(x2) & -p(x1)" ) ).
    u( ExistsIntroRule( _, hof"?y ((-p(x1) & -p(x2) & -p(y)) | (-p(x1) & p(x2) & p(y)) | (p(x1) & -p(x2) & p(y)) | (p(x1) & p(x2) & -p(y)))" ) ).
    qed
  println( p1 )
  val p2 = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"-p(x1)" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"p(x2)" ) ).
    b( AndIntroRule( _, _ ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"p(x2)" ) ).
    b( AndIntroRule( _, _ ) ).
    u( ContractionRule( _, hof"p(x2)" ) ).
    u( OrIntro2Rule( _, hof"-p(x1) & -p(x2) & -p(x2)" ) ).
    u( OrIntro1Rule( _, hof"p(x1) & -p(x2) & p(x2)" ) ).
    u( OrIntro1Rule( _, hof"p(x1) & p(x2) & -p(x2)" ) ).
    u( ExistsIntroRule( _, hof"?y ((-p(x1) & -p(x2) & -p(y)) | (-p(x1) & p(x2) & p(y)) | (p(x1) & -p(x2) & p(y)) | (p(x1) & p(x2) & -p(y)))" ) ).
    qed
  println( p2 )
  val p3 = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"p(x1)" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"-p(x2)" ) ).
    b( AndIntroRule( _, _ ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"p(x1)" ) ).
    b( AndIntroRule( _, _ ) ).
    u( ContractionRule( _, hof"p(x1)" ) ).
    u( OrIntro2Rule( _, hof"-p(x1) & -p(x2) & -p(x1) | (-p(x1) & p(x2) & p(x1))" ) ).
    u( OrIntro1Rule( _, hof"p(x1) & p(x2) & -p(x1)" ) ).
    u( ExistsIntroRule( _, hof"?y ((-p(x1) & -p(x2) & -p(y)) | (-p(x1) & p(x2) & p(y)) | (p(x1) & -p(x2) & p(y)) | (p(x1) & p(x2) & -p(y)))" ) ).
    qed
  println( p3 )
  val p4 = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"p(x1)" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"p(x2)" ) ).
    b( AndIntroRule( _, _ ) ).
    c( gapt.proofs.nd.TheoryAxiom( hof"-p(bFalse)" ) ).
    b( AndIntroRule( _, _ ) ).
    u( OrIntro2Rule( _, hof"(-p(x1) & -p(x2) & -p(bFalse)) | (-p(x1) & p(x2) & p(bFalse)) | (p(x1) & -p(x2) & p(bFalse))" ) ).
    u( ExistsIntroRule( _, hof"?y ((-p(x1) & -p(x2) & -p(y)) | (-p(x1) & p(x2) & p(y)) | (p(x1) & -p(x2) & p(y)) | (p(x1) & p(x2) & -p(y)))" ) ).
    qed
  println( p4 )
  val p = ProofBuilder.
    c( p4 ).
    c( p3 ).
    b( ExcludedMiddleRule( _, _, le"p(x2)" ) ).
    u( ContractionRule( _, hof"p(x1)" ) ).
    c( p2 ).
    c( p1 ).
    b( ExcludedMiddleRule( _, _, le"p(x2)" ) ).
    u( ContractionRule( _, hof"-p(x1)" ) ).
    b( ExcludedMiddleRule( _, _, le"p(x1)" ) ).
    u( ForallIntroRule( _, hof"!x2?y ((-p(x1) & -p(x2) & -p(y)) | (-p(x1) & p(x2) & p(y)) | (p(x1) & -p(x2) & p(y)) | (p(x1) & p(x2) & -p(y)))", hov"x2:bool" ) ).
    u( ForallIntroRule( _, hof"!x1!x2?y ((-p(x1) & -p(x2) & -p(y)) | (-p(x1) & p(x2) & p(y)) | (p(x1) & -p(x2) & p(y)) | (p(x1) & p(x2) & -p(y)))", hov"x1:bool" ) ).
    qed
  println( p )
  prooftool( p )
  /*
  val lam = ClassicalExtraction.extractCases( p4 )
  println( lam.toUntypedString )
  */
  val lam = ClassicalExtraction.extractCases( p )
  println( lam.toUntypedString )
  println( normalize( lam( bFalse )( bFalse ) ).toUntypedString )
  /*
  println( normalize( lam( bFalse )( bTrue ) ).toUntypedString )
  println( normalize( lam( bTrue )( bFalse ) ).toUntypedString )
  println( normalize( lam( bTrue )( bTrue ) ).toUntypedString )
  */
}

object higherOrderTypingProblem extends Script {
  // from gitter conversation
  import gapt.proofs.context.Context
  import gapt.proofs.nd.ClassicalExtraction

  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += Notation.Infix( "<=", Precedence.infixRel )
  ctx += Notation.Infix( "<", Precedence.infixRel )
  ctx += hoc"'<=': nat>nat>o"
  ctx += hoc"'<': nat>nat>o"
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  val p = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"?x (0 < x) | !y (0 <= y)" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"?x 0 < x" ) ).
    u( ExistsIntroRule( _, hof"?y y" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"!x!y (x <= y -> (x < y | x = y))" ) ).
    u( ForallElimBlock( _, List( le"0", le"s(0): nat" ) ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"!y (0 <= y)" ) ).
    u( ForallElimRule( _, le"s(0): nat" ) ).
    b( ImpElimRule( _, _ ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"0 < s(0)" ) ).
    u( ExistsIntroRule( _, hof"?y y" ) ).
    //u(ExistsIntroRule(_, hof"?x (0 < x)")).
    c( gapt.proofs.nd.LogicalAxiom( hof"!x -(x = s(x))" ) ).
    u( ForallElimRule( _, le"0: nat" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"0 = s(0)" ) ).
    b( NegElimRule( _, _ ) ).
    //u(BottomElimRule(_, hof"?x (0 < x)")).
    u( BottomElimRule( _, hof"?y y" ) ).
    t( OrElimRule( _, _, _ ) ).
    t( OrElimRule( _, _, _ ) ).
    qed
  println( p )
  prooftool( p )
  val lam = ClassicalExtraction.extractCases( p )
  println( lam )
}

object higherOrderTypingProblemSimple extends Script {
  // from gitter conversation
  import gapt.proofs.context.Context
  import gapt.proofs.nd.ClassicalExtraction

  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += hoc"P: nat>nat>o"
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  val p = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"?x P(0,x)" ) ).
    u( ExistsIntroRule( _, hof"?y y" ) ).
    qed
  println( p )
  prooftool( p )
  val lam = ClassicalExtraction.extractCases( p )
  println( lam )
}
object forallProvesNotExistsNot extends Script {
  import gapt.proofs.context.Context
  import gapt.proofs.nd.ClassicalExtraction

  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += hoc"P: nat>o"
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  val p = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"?x -P(x)" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"-P(x)" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"!x P(x)" ) ).
    u( ForallElimRule( _, le"x:nat" ) ).
    b( NegElimRule( _, _ ) ).
    b( ExistsElimRule( _, _ ) ).
    u( NegIntroRule( _, hof"?x -P(x)" ) ).
    qed
  println( p )
  prooftool( p )
  val lam = ClassicalExtraction.extractCases( p )
  println( lam )
}

object testCase extends Script {
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )

  implicit val ctxClassical = ClassicalExtraction.systemT( ctx )

  //val tryConst = hoc"try{?a ?c}: o > (?a > (?c > exn)) > (?a > (?c > exn))"
  //val catchConst = hoc"catch{?a ?c}: o > (exconj ?a ?c) > (exconj ?a ?c)"
  //val tryCatch = hoc"tryCatch{?a ?b ?c}: ?a > ?b > ?c > ?c > ?c"

  val sC = ctxClassical.constant("s").get
  val inlC = ctxClassical.constant("inl", List(ty"nat > (o > exn)", ty"exconj (nat) (o)")).get
  val inrC = ctxClassical.constant("inr", List(ty"nat > (o > exn)", ty"exconj (nat) (o)")).get
  val tryC = ctxClassical.constant("try", List(ty"nat", To)).get
  val catchC = ctxClassical.constant("catch", List(ty"nat", To)).get
  val tryCatchC = ctxClassical.constant("tryCatch", List(ty"nat > (o > exn)", ty"exconj (nat) (o)", ty"sum (nat > (o > exn)) (exconj (nat) (o))")).get
  val a = le"(y0: (nat > (o > exn)))"
  val b = le"(y1: (exconj (nat) (o)))"
  val tryT = inlC(tryC(hof"!(x:nat) -false", a))
  val catchT = inrC(catchC(hof"?(x:nat) false", b))
  val res = normalize(tryCatchC(a, b, tryT, catchT))
  println(res)
}

object testCase2 extends Script {
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += InductiveType( "bool", hoc"bFalse: bool", hoc"bTrue: bool" )
  val Some( bFalse ) = ctx.constant( "bFalse" )
  val Some( bTrue ) = ctx.constant( "bTrue" )
  val bIsTrue = hoc"p : bool>o"
  ctx += PrimitiveRecursiveFunction(
    bIsTrue,
    List(
      ( bIsTrue( bFalse ) -> hof"false" ),
      ( bIsTrue( bTrue ) -> hof"true" ) ) )( ctx )

  implicit val ctxClassical = ClassicalExtraction.systemT( ctx )

  //val tryConst = hoc"try{?a ?c}: o > (?a > (?c > exn)) > (?a > (?c > exn))"
  //val catchConst = hoc"catch{?a ?c}: o > (exconj ?a ?c) > (exconj ?a ?c)"
  //val tryCatch = hoc"tryCatch{?a ?b ?c}: ?a > ?b > ?c > ?c > ?c"

  val prf = ProofBuilder.
    c(gapt.proofs.nd.LogicalAxiom(hof"?(x:bool) p(x)")).
    u(OrIntro2Rule(_, hof"-(?(x:bool) p(x))")).
    c(gapt.proofs.nd.LogicalAxiom(hof"-(?(x:bool) p(x))")).
    //u(ForallElimRule(_, le"bFalse:bool")).
    u(OrIntro1Rule(_, hof"?(x:bool) p(x)")).
    b(ExcludedMiddleRule(_,_)).
    qed
  val lam = ClassicalExtraction.extractCases(prf)
  println(lam.toUntypedString)

  val sC = ctxClassical.constant("s").get
  val inlC = ctxClassical.constant("inl", List(ty"(o > exn)", ty"exconj (bool) (o)")).get
  val inrC = ctxClassical.constant("inr", List(ty"(o > exn)", ty"exconj (bool) (o)")).get
  val tryC = ctxClassical.constant("try", List(ty"bool", To)).get
  val catchC = ctxClassical.constant("catch", List(ty"bool", To)).get
  val tryCatchC = ctxClassical.constant("tryCatch", List(ty"bool > (o > exn)", ty"exconj (bool) (o)", ty"sum (o > exn) (exconj (bool) (o))")).get
  val a = le"(y0: (bool > (o > exn)))"
  val b = le"(y1: (exconj (bool) (o)))"
  val tmp = hof"-false"
  println(tmp)
  val tryT = inlC(tryC(hof"!(x:bool) -p(x)", a)(le"bTrue:bool"))
  val catchT = inrC(catchC(hof"?(x:bool) p(x)", b))
  val res = normalize(tryCatchC(a, b, tryT, catchT))
  println(res.toUntypedString)
}

object zIffaAndb extends Script {

  import gapt.proofs.context.Context
  import gapt.proofs.nd.ClassicalExtraction
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += InductiveType( "bool", hoc"bFalse: bool", hoc"bTrue: bool" )
  val Some( bFalse ) = ctx.constant( "bFalse" )
  val Some( bTrue ) = ctx.constant( "bTrue" )
  val bIsTrue = hoc"p : bool>o"
  ctx += PrimitiveRecursiveFunction(
    bIsTrue,
    List(
      ( bIsTrue( bFalse ) -> hof"false" ),
      ( bIsTrue( bTrue ) -> hof"true" ) ) )( ctx )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  val p1 = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"-(p(x) & p(y))" ) ).
    c( gapt.proofs.nd.LogicalAxiom( hof"p(x) & p(y)" ) ).
    b(NegElimRule(_,_)).
    u(BottomElimRule(_, hof"p(bFalse)")).
    u(ImpIntroRule(_, Ant(1))).
    qed
  val p2 = ProofBuilder.
    c( gapt.proofs.nd.TheoryAxiom( hof"-p(bFalse)" ) ).
    c(gapt.proofs.nd.LogicalAxiom(hof"p(bFalse)")).
    b(NegElimRule(_,_)).
    u(BottomElimRule(_, hof"p(x) & p(y)")).
    u(ImpIntroRule(_, Ant(0))).
    qed
  val q1 = ProofBuilder.
    c(p1).
    c(p2).
    b(AndIntroRule(_, _)).
    u(ExistsIntroRule(_, hof"?z (((p(x) & p(y)) -> p(z)) & (p(z) -> (p(x) & p(y))))")).
    qed

  val p3 = ProofBuilder.
    c( gapt.proofs.nd.TheoryAxiom( hof"p(bTrue)" ) ).
    u(WeakeningRule(_, hof"p(x) & p(y)")).
    u(ImpIntroRule(_, Ant(0))).
    qed
  val p4 = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom(hof"p(x) & p(y)")).
    u(WeakeningRule(_, hof"p(bTrue)")).
    u(ImpIntroRule(_, Ant(0))).
    qed
  val q2 = ProofBuilder.
    c(p3).
    c(p4).
    b(AndIntroRule(_,_)).
    u(ExistsIntroRule(_, hof"?z (((p(x) & p(y)) -> p(z)) & (p(z) -> (p(x) & p(y))))")).
    qed

  val p = ProofBuilder.
    c(q2).
    c(q1).
    b(ExcludedMiddleRule(_,_)).
    u(ForallIntroRule(_, hov"y:bool", hov"y:bool")).
    u(ForallIntroRule(_, hov"x:bool", hov"x:bool")).
    qed

  prooftool(p)
  val lam = ClassicalExtraction.extractCases(p)
  println(lam.toUntypedString)
}

object zIffaAndbShortCircuit extends Script {

  import gapt.proofs.context.Context
  import gapt.proofs.nd.ClassicalExtraction
  var ctx = Context.default
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
  ctx += InductiveType( "bool", hoc"bFalse: bool", hoc"bTrue: bool" )
  val Some( bFalse ) = ctx.constant( "bFalse" )
  val Some( bTrue ) = ctx.constant( "bTrue" )
  val bIsTrue = hoc"p : bool>o"
  ctx += PrimitiveRecursiveFunction(
    bIsTrue,
    List(
      ( bIsTrue( bFalse ) -> hof"false" ),
      ( bIsTrue( bTrue ) -> hof"true" ) ) )( ctx )
  implicit var ctxClassical = ClassicalExtraction.systemT( ctx )
  val p1 = ProofBuilder.
    c( gapt.proofs.nd.LogicalAxiom( hof"p(x) & p(y)" ) ).
    u(AndElim2Rule(_)).
    u(ImpIntroRule(_, Ant(0))).
    qed
  val p2 = ProofBuilder.
    c(gapt.proofs.nd.LogicalAxiom(hof"p(x)")).
    c(gapt.proofs.nd.LogicalAxiom(hof"p(y)")).
    b(AndIntroRule(_, _)).
    u(ImpIntroRule(_, Ant(1))).
    qed
  val q1 = ProofBuilder.
    c(p1).
    c(p2).
    b(AndIntroRule(_, _)).
    u(ExistsIntroRule(_, hof"?z (((p(x) & p(y)) -> p(z)) & (p(z) -> (p(x) & p(y))))")).
    qed

  val p3 = ProofBuilder.
    c(gapt.proofs.nd.LogicalAxiom(hof"-p(x)")).
    c( gapt.proofs.nd.LogicalAxiom( hof"p(x) & p(y)" ) ).
    u(AndElim1Rule(_)).
    b(NegElimRule(_,_)).
    u(BottomElimRule(_, hof"p(bFalse)")).
    u(ImpIntroRule(_, Ant(1))).
    qed
  val p4 = ProofBuilder.
    c( gapt.proofs.nd.TheoryAxiom( hof"-p(bFalse)" ) ).
    c( gapt.proofs.nd.LogicalAxiom(hof"p(bFalse)")).
    b(NegElimRule(_,_)).
    u(BottomElimRule(_, hof"p(x) & p(y)")).
    u(ImpIntroRule(_, Ant(0))).
    qed
  val q2 = ProofBuilder.
    c(p3).
    c(p4).
    b(AndIntroRule(_,_)).
    u(ExistsIntroRule(_, hof"?z (((p(x) & p(y)) -> p(z)) & (p(z) -> (p(x) & p(y))))")).
    qed

  val p = ProofBuilder.
    c(q1).
    c(q2).
    b(ExcludedMiddleRule(_,_)).
    u(ForallIntroRule(_, hov"y:bool", hov"y:bool")).
    u(ForallIntroRule(_, hov"x:bool", hov"x:bool")).
    qed

  prooftool(p)
  val lam = ClassicalExtraction.extractCases(p)
  println(lam.toUntypedString)
}
