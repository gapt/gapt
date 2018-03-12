package gapt.expr.hol

import HOLPosition._
import gapt.expr._

import org.specs2.mutable._

class HOLPositionTest extends Specification {
  "HOLPositions" should {
    "be computed correctly" in {
      val x = Var( "x", Ti )
      val y = Var( "y", Ti )
      val f = Const( "f", Ti ->: Ti )
      val c = Const( "c", Ti )
      val P = Const( "P", Ti ->: To )
      val Px = Atom( P, List( x ) )
      val Pfc = Atom( P, List( App( f, c ) ) )

      getPositions( Px ) must beEqualTo( List( HOLPosition( Nil ), HOLPosition( 1 ), HOLPosition( 2 ) ) )
      replace( Px, HOLPosition( 2 ), App( f, c ) ) must beEqualTo( Pfc )
    }
  }

  "get" should {
    "be total" in {
      FOLFunction( "f", FOLConst( "c" ) ).get( HOLPosition( 1, 2, 1, 2 ) ) must beNone
    }
  }
}
