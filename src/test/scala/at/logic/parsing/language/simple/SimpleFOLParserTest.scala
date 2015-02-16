/*
 * SimpleFOLParser.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.parsing.language.simple

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.language.hol.{HOLVar,HOLConst}
import at.logic.language.fol._
import at.logic.language.lambda.symbols.StringSymbol
import at.logic.parsing.readers.StringReader

@RunWith(classOf[JUnitRunner])
class SimpleFOLParserTest extends SpecificationWithJUnit {
  private class MyParser(input: String) extends StringReader(input) with SimpleFOLParser


  val var1 = FOLVar(new StringSymbol("x1"))
  val const1 = FOLConst(new StringSymbol("c1"))
  val var2 = FOLVar(new StringSymbol("x2"))
  val atom1 = FOLAtom(new StringSymbol("A"),var1::var2::const1::Nil)
  val var3 = FOLAtom(new StringSymbol("X3"), Nil)
  val func1 = FOLFunction(new StringSymbol("f"), var1::var2::const1::Nil)
  val and1 = FOLAnd(atom1, var3)
  val or1 = FOLOr(atom1, var3)
  val imp1 = FOLImp(atom1, var3)
  val neg1 = FOLNeg(atom1)
  val ex1 = FOLExVar(var1,atom1)
  val all1 = FOLAllVar(var1,atom1)
  val npx = FOLNeg(FOLAtom(new StringSymbol("p"), FOLVar(new StringSymbol("x"))::Nil))

  "SimpleFOLParser" should {
    "parse correctly a variable" in {
        (new MyParser("x1").getTerm()) must beEqualTo (var1)
    }
    "parse correctly an constant" in {
        (new MyParser("c1").getTerm()) must beEqualTo (const1)
    }
    "parse correctly an atom" in {
        (new MyParser("A(x1, x2, c1)").getTerm()) must beEqualTo (atom1)
    }
    "parse correctly a formula" in {
        (new MyParser("X3").getTerm()) must beLike {case x: FOLFormula => ok}
        (new MyParser("X3").getTerm()) must beEqualTo (var3)
    }
    "parse correctly a function 1" in {
      (new MyParser("f(x1)").getTerm()) must beEqualTo (FOLFunction(StringSymbol("f"), var1::Nil))
    }
    "parse correctly a function 2" in {
        (new MyParser("f(x1, x2, c1)").getTerm()) must beEqualTo (func1)
    }
    "parse correctly an and" in {
        (new MyParser("And A(x1, x2, c1) X3").getTerm()) must beEqualTo (and1)
    }
    "parse correctly an or" in {
        (new MyParser("Or A(x1, x2, c1) X3").getTerm()) must beEqualTo (or1)
    }
    "parse correctly an imp" in {
        (new MyParser("Imp A(x1, x2, c1) X3").getTerm()) must beEqualTo (imp1)
    }
    "parse correctly an neg" in {
        (new MyParser("Neg A(x1, x2, c1)").getTerm()) must beEqualTo (neg1)
    }
    "parse correctly an exists" in {
        (new MyParser("Exists x1 A(x1, x2, c1)").getTerm()) must beEqualTo (ex1)
    }
    "parse correctly a forall" in {
        (new MyParser("Forall x1 A(x1, x2, c1)").getTerm()) must beEqualTo (all1)
    }
    "reject the empty string" in {
      (new MyParser("").getTerm()) must throwAn[Exception]
    }
    "reject the string p(X)" in {
      (new MyParser("p(X)").getTerm()) must throwAn[Exception]
    }
  }
}
