package gapt.examples

import gapt.proofs.nd._
import gapt.expr.{ TBase, _ }
import gapt.proofs.{ Ant, Checkable, Context, Sequent }
import gapt.proofs.Context.{ InductiveType, PrimRecFun }

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
    print( proof ); print( m1 ); print( " of type " ); print( m1.ty )
    println(); println()
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

  val b1 = LogicalAxiom( hof"x = 0" )
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

  val b1 = LogicalAxiom( hof"-(x = 0)" )
  val b2 = LogicalAxiom( hof"x = 0" )
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

  val b1 = LogicalAxiom( hof"-(x = 0)" )
  val b2 = LogicalAxiom( hof"x = 0" )
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

  val a1 = LogicalAxiom( hof"-(x = 0)" )
  val a2 = LogicalAxiom( hof"x = 0" )
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

  val a1 = LogicalAxiom( hof"-(x = 0)" )
  val a2 = LogicalAxiom( hof"x = 0" )
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

  val l = ProofBuilder.
    c( LogicalAxiom( hof"!x P x" ) ).
    u( ForallElimRule( _, le"n: nat" ) ).
    u( ExistsIntroRule( _, hof"?x P x" ) ).
    u( OrIntro1Rule( _, hof"?x -(P x)" ) ).
    qed
  classicalExtractionTest( l )

  val r = ProofBuilder.
    c( LogicalAxiom( hof"?x -(P x)" ) ).
    u( OrIntro2Rule( _, hof"?x P x" ) ).
    qed
  classicalExtractionTest( r )
}

object example9 extends Script {

  implicit var ctx = Context()
  ctx += InductiveType(
    ty"nat",
    hoc"0 : nat",
    hoc"s : nat > nat" )
  ctx += hoc"P: nat > o"

  val p = ProofBuilder.
    c( LogicalAxiom( hof"?x P x" ) ).
    u( OrIntro1Rule( _, hof"-(?x P x)" ) ).
    c( LogicalAxiom( hof"-(?x P x)" ) ).
    u( OrIntro2Rule( _, hof"?x P x" ) ).
    b( ExcludedMiddleRule( _, Ant( 0 ), _, Ant( 0 ) ) ).
    qed
  classicalExtractionTest( p )
}