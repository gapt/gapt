package at.logic.gapt.proofs.lkskNew

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Sequent, Ant, Suc }
import org.specs2.mutable._

class LKskNewTest extends Specification {
  // Daniel's PhD thesis, p. 39
  "example 4.1.3" in {
    val S = FOLAtomConst( "S", 1 )
    val f = Const( "f", ( Ti -> To ) -> Ti )
    val x = FOLVar( "x" )
    val z = FOLVar( "z" )
    val Y = Var( "Y", Ti -> To )
    val X = Var( "X", Ti -> To )

    val p1 = Axiom(
      Seq( Abs( x, -S( x ) ) ),
      Seq( Abs( x, -S( x ) ) ),
      S( f( Abs( x, -S( x ) ) ) )
    )
    val p2 = NegLeft( p1, Suc( 0 ) )
    val p3 = NegRight( p2, Ant( 0 ) )
    val p4 = ImpRight( p3, Ant( 0 ), Suc( 0 ) )
    val p5 = AllSkRight( p4, Suc( 0 ), All( z, S( z ) --> -( -S( z ) ) ), f )
    val p6 = ExSkRight( p5, Suc( 0 ), Ex( Y, All( z, S( z ) --> -Y( z ) ) ), Abs( x, -S( x ) ) )
    val p7 = AllSkRight( p6, Suc( 0 ), All( X, Ex( Y, All( z, X( z ) --> -Y( z ) ) ) ), S )
    p7.conclusion must_== ( Sequent() :+ ( Seq() ->
      All( X, Ex( Y, All( z, X( z ) --> -Y( z ) ) ) ) ) )
  }

  "and left" should {
    "require the same labels" in {
      val p = FOLAtom( "p" )
      val Seq( c, d ) = Seq( "c", "d" ) map { FOLConst( _ ) }
      val p1 = Axiom( Seq( c ), Seq( d ), p )
      val p2 = NegLeft( p1, Suc( 0 ) )
      AndLeft( p2, Ant( 0 ), Ant( 1 ) ) should throwAn[IllegalArgumentException]
    }
  }
}