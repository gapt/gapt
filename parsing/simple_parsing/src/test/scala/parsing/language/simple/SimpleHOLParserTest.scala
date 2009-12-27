/*
 * SimpleHOLParser.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.parsing.language.simple

import org.specs._
import org.specs.runner._
import at.logic.language.hol.propositions._
import at.logic.language.hol.quantifiers._
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.hol.propositions.Definitions._
import at.logic.language.hol.propositions.ImplicitConverters._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.lambda.types._
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.parsing.readers.StringReader

class SimpleHOLParserTest extends SpecificationWithJUnit {
  private class MyParser(input: String) extends StringReader(input) with SimpleHOLParser
    "SimpleHOLParser" should {
        val var1 = HOLVar(new VariableStringSymbol("x1"), i->(i->i))
        "parse correctly a variable" in {
            (new MyParser("x1: (i -> (i -> i))").getTerm()) must beEqual (var1)
        }
        val const1 = HOLConst(new ConstantStringSymbol("c1"), i->i)
        "parse correctly an constant" in {    
            (new MyParser("c1: (i -> i)").getTerm()) must beEqual (const1)
        }
        val var2 = HOLVar(new VariableStringSymbol("x2"), i)
        val atom1 = Atom(new ConstantStringSymbol("a"),var1::var2::const1::Nil)
        "parse correctly an atom" in {  
            (new MyParser("a(x1: (i -> (i -> i)), x2: i, c1: (i -> i))").getTerm()) must beEqual (atom1)
        }
        val var3 = HOLVarFormula(new VariableStringSymbol("x3"))
        "parse correctly a formula variable" in {
            (new MyParser("x3: o").getTerm()) must beLike {case x: Formula => true}
        }
        "parse correctly a formula constant" in {
            (new MyParser("c: o").getTerm()) must beLike {case x: Formula => true}
        }
        val f1 = Function(ConstantStringSymbol("f"), Var(ConstantStringSymbol("a"), i, hol)::Nil,i)
        /*"parse correctly a function" in {
          (new MyParser("f(a:i):i")).getTerm must beEqual (f1)
        }*/
        val and1 = And(atom1, var3)
        "parse correctly an and" in {
            (new MyParser("And a(x1: (i -> (i -> i)), x2: i, c1: (i -> i)) x3: o").getTerm()) must beEqual (and1)
        }
        val or1 = Or(atom1, var3)
        "parse correctly an or" in {
            (new MyParser("Or a(x1: (i -> (i -> i)), x2: i, c1: (i -> i)) x3: o").getTerm()) must beEqual (or1)
        }
        val imp1 = Imp(atom1, var3)
        "parse correctly an imp" in {
            (new MyParser("Imp a(x1: (i -> (i -> i)), x2: i, c1: (i -> i)) x3: o").getTerm()) must beEqual (imp1)
        }
        val neg1 = Neg(atom1)
        "parse correctly an neg" in {
            (new MyParser("Neg a(x1: (i -> (i -> i)), x2: i, c1: (i -> i))").getTerm()) must beEqual (neg1)
        }
        val ex1 = ExVar(var1,atom1)
        "parse correctly an exists" in {
            (new MyParser("Exists x1: (i -> (i -> i)) a(x1: (i -> (i -> i)), x2: i, c1: (i -> i))").getTerm()) must beEqual (ex1)
        }
        val all1 = AllVar(var1,atom1)
        "parse correctly a forall" in {
            (new MyParser("Forall x1: (i -> (i -> i)) a(x1: (i -> (i -> i)), x2: i, c1: (i -> i))").getTerm()) must beEqual (all1)
        }
    }
    
}
