package at.logic.algorithms.fol

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.language.fol
import at.logic.language.hol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.types.{To, Ti}
import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.hol.HOLFactory

/**
 * Created by marty on 3/10/14.
 */
@RunWith(classOf[JUnitRunner])
class fol2holTest extends SpecificationWithJUnit {
  "Conversion from fol to hol" should {
    "work for some simple terms" in {
      val fterm = fol.Function(ConstantStringSymbol("f"), List(
                    fol.FOLConst(ConstantStringSymbol("q1")),
                    fol.FOLVar(VariableStringSymbol("x"))))
      val hterm = fol2hol(fterm)
      hterm must beEqualTo(fterm)
      hterm.factory must beEqualTo(hol.HOLFactory)

      val rterm = recreateWithFactory(fterm, hol.HOLFactory)
      rterm must beEqualTo(fterm)
      rterm.factory must beEqualTo(hol.HOLFactory)
    }

    "allow substitution of a fol term into a hol term" in {
      val p = hol.HOLConst(ConstantStringSymbol("P"), Ti() -> ((Ti() -> Ti()) -> To()))
      val x = hol.HOLVar(VariableStringSymbol("x"), Ti())
      val y = hol.HOLVar(VariableStringSymbol("y"), Ti())

      val hterm = hol.Atom(ConstantStringSymbol("P"),List(y, hol.HOLAbs(x,x)))

      val fterm = fol.FOLConst(ConstantStringSymbol("c"))

      val fsub = Substitution[hol.HOLExpression](fol.FOLVar(VariableStringSymbol("y")), fterm)


      /*TODO: Martin expected this to fail, but it doesn't (app takes the factory of the first parameter, which is fol
        after the substitution, so the lambda x.x should be created by the fol factory and fail).
       */
      val sterm = fsub(hterm)
      sterm.factory must beEqualTo(HOLFactory) //surprisingly enough, this does not fail

      println(sterm)
      val f2hterm = fol2hol(fsub.asInstanceOf[Substitution[fol.FOLExpression]])(hterm)

      f2hterm.factory must beEqualTo(hol.HOLFactory)

      recreateWithFactory(fsub, hol.HOLFactory)(hterm).factory must beEqualTo(hol.HOLFactory)

    }

    //TODO: add test cases
  }
}
