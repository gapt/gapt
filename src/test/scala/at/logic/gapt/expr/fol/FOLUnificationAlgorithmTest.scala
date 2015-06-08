/*
 * FOLUnificationAlgorithmTest.scala
 *
 */

package at.logic.gapt.expr.fol

import at.logic.gapt.expr._
import org.specs2.mutable._

class FOLUnificationAlgorithmTest extends Specification {

  "UnificationBasedFOLMatchingAlgorithm" should {
    "match correctly the lambda expressions f(x1, x2, c) and f(a,b,c)" in {
      val x = FOLVar( "x" )
      val a = FOLConst( "a" )
      val b = FOLConst( "b" )
      val term = FOLFunction( "f", x :: x :: Nil )
      val posInstance = FOLFunction( "f", a :: b :: Nil )

      val sub = FOLUnificationAlgorithm.unify( term, posInstance )
      sub must beEqualTo( Nil )
    }
  }

}
