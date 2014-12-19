package at.logic.algorithms.fol

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.language.fol
import at.logic.language.hol
import at.logic.language.lambda.types.{To, Ti}
import at.logic.language.hol.{HOLConst, HOLFactory}

/**
 * Created by marty on 3/10/14.
 */
@RunWith(classOf[JUnitRunner])
class fol2holTest extends SpecificationWithJUnit {
  "Conversion from fol to hol" should {
    "work for some simple terms" in {
      val fterm = fol.Function("f", List(
                    fol.FOLConst("q1"),
                    fol.FOLVar("x")))
      val hterm = fol2hol(fterm)
      hterm must beEqualTo(fterm)
      hterm.factory must beEqualTo(hol.HOLFactory)

      val rterm = recreateWithFactory(fterm, hol.HOLFactory)
      rterm must beEqualTo(fterm)
      rterm.factory must beEqualTo(hol.HOLFactory)
    }

    "allow substitution of a fol term into a hol term" in {
      val p = hol.HOLConst("P", Ti -> ((Ti -> Ti) -> To))
      val x = hol.HOLVar("x", Ti)
      val y = hol.HOLVar("y", Ti)

      val hterm = hol.Atom(HOLConst("P", Ti -> ((Ti -> Ti) -> To)),List(y, hol.HOLAbs(x,x)))

      val fterm = fol.FOLConst("c")

      val fsub = hol.Substitution(fol.FOLVar("y"), fterm)


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
