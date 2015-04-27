package at.logic.gapt.language.fol.algorithms

import at.logic.gapt.language.fol._
import at.logic.gapt.language.hol._
import at.logic.gapt.expr.types.{ Ti, To }
import org.junit.runner.RunWith
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner

/**
 * Created by marty on 3/10/14.
 */
@RunWith( classOf[JUnitRunner] )
class fol2holTest extends SpecificationWithJUnit {
  "Conversion from fol to hol" should {
    "work for some simple terms" in {
      val fterm = FOLFunction( "f", List(
        FOLConst( "q1" ),
        FOLVar( "x" ) ) )
      val hterm = fol2hol( fterm )
      hterm must beEqualTo( fterm )
      hterm.factory must beEqualTo( HOLFactory )

      val rterm = recreateWithFactory( fterm, HOLFactory )
      rterm must beEqualTo( fterm )
      rterm.factory must beEqualTo( HOLFactory )
    }

    "allow substitution of a fol term into a hol term" in {
      val p = HOLConst( "P", Ti -> ( ( Ti -> Ti ) -> To ) )
      val x = HOLVar( "x", Ti )
      val y = HOLVar( "y", Ti )

      val hterm = HOLAtom( HOLConst( "P", Ti -> ( ( Ti -> Ti ) -> To ) ), List( y, HOLAbs( x, x ) ) )

      val fterm = FOLConst( "c" )

      val fsub = HOLSubstitution( FOLVar( "y" ), fterm )

      /*TODO: Martin expected this to fail, but it doesn't (app takes the factory of the first parameter, which is fol
        after the substitution, so the lambda x.x should be created by the fol factory and fail).

        in the new lambda calculus, this really fails as expected
       */
      //val sterm = fsub(hterm)
      //sterm.factory must beEqualTo(HOLFactory) //surprisingly enough, this does not fail

      //println(sterm)
      //TODO: add tests for converting substitutions back in
      //val f2hterm = fol2hol(fsub.asInstanceOf[Substitution[fol.FOLExpression]])(hterm)

      //f2hterm.factory must beEqualTo(hol.HOLFactory)

      //recreateWithFactory(fsub, hol.HOLFactory)(hterm).factory must beEqualTo(hol.HOLFactory)
      ok
    }

    //TODO: add test cases
  }
}
