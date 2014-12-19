/*
 * SimpleHOLParser.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.parsing.language.simple

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.language.hol._
import at.logic.language.lambda.symbols.StringSymbol
import at.logic.parsing.readers.StringReader
import at.logic.language.lambda.types._

@RunWith(classOf[JUnitRunner])
class SimpleHOLParserTest extends SpecificationWithJUnit {
  private class MyParser(input: String) extends StringReader(input) with SimpleHOLParser
    "SimpleHOLParser" should {
        val var1 = HOLVar(StringSymbol("x1"), Ti->(Ti->Ti))
        "parse correctly a variable" in {
            (new MyParser("x1: (i -> (i -> i))").getTerm()) must beEqualTo (var1)
        }
        val const1 = HOLConst(StringSymbol("c1"), Ti->Ti)
        "parse correctly an constant" in {    
            (new MyParser("c1: (i -> i)").getTerm()) must beEqualTo (const1)
        }
        val var2 = HOLVar(StringSymbol("x2"), Ti)
        val atom1 = Atom(HOLConst(StringSymbol("a"), var1.exptype -> (var2.exptype -> (const1.exptype -> To))  ),var1::var2::const1::Nil)
        "parse correctly an atom" in {  
            (new MyParser("a(x1: (i -> (i -> i)), x2: i, c1: (i -> i))").getTerm()) must beEqualTo (atom1)
        }
        "parse correctly an abs" in {
            (new MyParser("Abs x1: (i -> (i -> i)) a(x1: (i -> (i -> i)), x2: i, c1: (i -> i))").getTerm()) must beEqualTo (HOLAbs(var1, atom1))
        }
        val var3 = Atom(HOLVar(StringSymbol("x3"), To))
        "parse correctly a formula variable" in {
            (new MyParser("x3: o").getTerm()) must beLike {case x: Formula => ok}
        }
        "parse correctly a formula constant" in {
            (new MyParser("c: o").getTerm()) must beLike {case x: Formula => ok}
        }
        val f1 = Function(HOLConst(StringSymbol("f"), Ti -> Ti), HOLConst(StringSymbol("a"), Ti)::Nil)
        "parse correctly a function" in {
          (new MyParser("f(a:i):i")).getTerm must beEqualTo (f1)
        }
        val f2 = Function(HOLVar(StringSymbol("x"), Ti -> Ti), HOLConst(StringSymbol("a"), Ti)::Nil)
        "parse correctly a function variable 1" in {
          val term = (new MyParser("x(a:i):i")).getTerm
          term must beEqualTo (f2)
        }
        val and1 = And(atom1, var3)
        "parse correctly an and" in {
            (new MyParser("And a(x1: (i -> (i -> i)), x2: i, c1: (i -> i)) x3: o").getTerm()) must beEqualTo (and1)
        }
        val or1 = Or(atom1, var3)
        "parse correctly an or" in {
            (new MyParser("Or a(x1: (i -> (i -> i)), x2: i, c1: (i -> i)) x3: o").getTerm()) must beEqualTo (or1)
        }
        val imp1 = Imp(atom1, var3)
        "parse correctly an imp" in {
            (new MyParser("Imp a(x1: (i -> (i -> i)), x2: i, c1: (i -> i)) x3: o").getTerm()) must beEqualTo (imp1)
        }
        val neg1 = Neg(atom1)
        "parse correctly an neg" in {
            (new MyParser("Neg a(x1: (i -> (i -> i)), x2: i, c1: (i -> i))").getTerm()) must beEqualTo (neg1)
        }
        val ex1 = ExVar(var1,atom1)
        "parse correctly an exists" in {
            (new MyParser("Exists x1: (i -> (i -> i)) a(x1: (i -> (i -> i)), x2: i, c1: (i -> i))").getTerm()) must beEqualTo (ex1)
        }
        val all1 = AllVar(var1,atom1)
        "parse correctly a forall" in {
            (new MyParser("Forall x1: (i -> (i -> i)) a(x1: (i -> (i -> i)), x2: i, c1: (i -> i))").getTerm()) must beEqualTo (all1)
        }
        val str = """p(x_10:i,m(x_3:i,m(m(p(x_4:i,one:i):i,p(x_5:i,one:i):i):i):i):i):i"""
        "parse correctly a complex term" in {
            (new MyParser(str).getTerm()) must not(throwAn[Exception])
        }
    }
    
}
