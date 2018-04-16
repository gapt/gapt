package gapt.expr.hol

import gapt.expr._
import org.specs2.mutable._

class UtilsTest extends Specification {
  "dualize" should {
    "be computed correctly" in {
      val x = FOLVar( "x" )
      val Px = FOLAtom( "P", x )
      val Qx = FOLAtom( "Q", x )

      val F = All( x, And( Px, Neg( Qx ) ) )
      val G = Ex( x, Or( Neg( Px ), Qx ) )

      dualize( F ) must beEqualTo( G )
    }
  }
}
