package at.logic.gapt.proofs.lkskNew

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Sequent, Ant, Suc }
import org.specs2.mutable._

class LKskNewTest extends Specification {
  // Daniel's PhD thesis, p. 39
  "example 4.1.3" in {
    val S = Const( "S", Ti -> To )
    val f = Const( "f", ( Ti -> To ) -> Ti )
    val x = FOLVar( "x" )
    val z = FOLVar( "z" )
    val Y = Var( "Y", Ti -> To )
    val X = Var( "X", Ti -> To )

    val p1 = LogicalAxiom(
      Seq( Abs( x, -S( x ) ) ),
      S( f( Abs( x, -S( x ) ) ) ).asInstanceOf[HOLAtom]
    )
    val p2 = NegLeft( p1, Suc( 0 ) )
    val p3 = NegRight( p2, Ant( 0 ) )
    val p4 = ImpRight( p3, Ant( 0 ), Suc( 0 ) )
    val p5 = AllRight( p4, Suc( 0 ), All( z, S( z ) --> -( -S( z ) ) ), f )
    val p6 = ExRight( p5, Suc( 0 ), Ex( Y, All( z, S( z ) --> -Y( z ) ) ), Abs( x, -S( x ) ) )
    val p7 = AllRight( p6, Suc( 0 ), All( X, Ex( Y, All( z, X( z ) --> -Y( z ) ) ) ), S )
    p7.conclusion must_== ( Sequent() :+ ( Seq() ->
      All( X, Ex( Y, All( z, X( z ) --> -Y( z ) ) ) ) ) )
  }

  "and left" should {
    "require the same labels" in {
      val Seq( p, q ) = Seq( "p", "q" ) map { FOLAtom( _ ) }
      val p1 = LogicalAxiom( Seq( p ), p )
      val p2 = WeakeningLeft( p1, Seq( q ) -> p )
      AndLeft( p2, Ant( 0 ), Ant( 1 ) ) should throwAn[IllegalArgumentException]
    }
  }
}