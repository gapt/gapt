/*
 * hol2folTest.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.fol

import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.language.fol
import at.logic.language.hol.{Neg => HOLNeg, And => HOLAnd, Or => HOLOr, Imp => HOLImp, Function => HOLFunction, Atom => HOLAtom, ExVar => HOLExVar, AllVar => HOLAllVar}
import at.logic.language.hol.HOLVarFormula
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types._
import at.logic.language.lambda.symbols._
import at.logic.parsing.readers.StringReader
import at.logic.parsing.language.simple.SimpleHOLParser
import at.logic.parsing.language.simple.SimpleFOLParser
import hol2fol._

import scala.collection.mutable
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.fol.FOLVar

@RunWith(classOf[JUnitRunner])
class hol2folTest extends SpecificationWithJUnit {
  private class MyParserHOL(input: String) extends StringReader(input) with SimpleHOLParser
  private class MyParserFOL(input: String) extends StringReader(input) with SimpleFOLParser
  def imap = mutable.Map[LambdaExpression, ConstantStringSymbol]() // the scope for most tests is just the term itself
  def iid = new {var idd = 0; def nextId = {idd = idd+1; idd}}
  "HOL terms" should {
    "be correctly reduced into FOL terms for" in {
      "Atom - A(x:(i->i), a:o->i)" in {
        reduceHolToFol(new MyParserHOL("A(x:(i->i), a:(o->i))").getTerm(),imap,iid) must beEqualTo (new MyParserFOL("A(x, a)").getTerm())
        convertHolToFol(new MyParserHOL("A(x:i, a:i)").getTerm()) must beEqualTo (new MyParserFOL("A(x, a)").getTerm())
      }
      "Function - f(x:(i->i), a:(o->i)):(o->o)" in {
        reduceHolToFol(new MyParserHOL("f(x:(i->i), a:(o->i)):(o->o)").getTerm(),imap,iid) must beEqualTo (new MyParserFOL("f(x, a)").getTerm())
        convertHolToFol.convertTerm(new MyParserHOL("f(x:i, a:i):i").getTerm()) must beEqualTo (new MyParserFOL("f(x, a)").getTerm())
      }
      "Connective - And A(x:(i->i), a:(o->i)) B(x:(i->i), b:(o->i))" in {
        reduceHolToFol(new MyParserHOL("And A(x:(i->i), a:(o->i)) B(x:(i->i), b:(o->i))").getTerm(),imap,iid) must beEqualTo (new MyParserFOL("And A(x, a) B(x, b)").getTerm())
        convertHolToFol(new MyParserHOL("And A(x:i, a:i) B(x:i, b:i)").getTerm()) must beEqualTo (new MyParserFOL("And A(x, a) B(x, b)").getTerm())
      }
      "Abstraction - f(Abs x:(i->i) A(x:(i->i), a:(o->i))):(o->o)" in {
        reduceHolToFol(new MyParserHOL("f(Abs x:(i->i) A(x:(i->i), a:(o->i))):(o->o)").getTerm(),imap,iid) must beEqualTo (new MyParserFOL("f(q_{1})").getTerm())
      }
      "Abstraction - f(Abs x:(i->i) A(x:(i->i), y:(o->i))):(o->o)" in {
        val red = reduceHolToFol(new MyParserHOL("f(Abs x:(i->i) A(x:(i->i), y:(o->i))):(o->o)").getTerm(),imap,iid)
        val fol = (new MyParserFOL("f(q_{1}(y))").getTerm())
        red must beEqualTo (fol)
      }
      "Two terms - f(Abs x:(i->i) A(x:(i->i), y:(o->i))):(o->o) and g(Abs x:(i->i) A(x:(i->i), z:(o->i))):(o->o)" in {
        println("two terms")
        val map = mutable.Map[LambdaExpression, ConstantStringSymbol]()
        var id = new {var idd = 0; def nextId = {idd = idd+1; idd}}
        val t1 = new MyParserHOL("f(Abs x:(i->i) A(x:(i->i), y:(o->i))):(o->o)").getTerm()
        val t2 = new MyParserHOL("g(Abs x:(i->i) A(x:(i->i), z:(o->i))):(o->o)").getTerm()
        val r1 = reduceHolToFol(t1,map,id)
        println("map="+map)
        val r2 = reduceHolToFol(t2,map,id)
        val s1 = new MyParserFOL("f(q_{1}(y))").getTerm()
        val s2 = new MyParserFOL("g(q_{1}(z))").getTerm()
        println(t1)
        println(t2)
        println(r1)
        println(r2)
        (r1::r2::Nil) must beEqualTo(s1::s2::Nil)
      }
      "Correctly convert from type o to i on the termlevel" in {
        val List(sp,sq) = List("P","Q").map(ConstantStringSymbol)
        val List(x,y) = List("x","y").map(x => HOLVarFormula(VariableStringSymbol(x)))
        val f1 = HOLAtom(sp,List(HOLImp(x,y)))
        val f2 = fol.Atom(sp, List(fol.Function(ImpSymbol,
          List(fol.FOLConst(ConstantStringSymbol("x")),
               fol.FOLConst(ConstantStringSymbol("y"))))))
        val red = reduceHolToFol(f1)
        /*
        red match {
          case HOLAtom(_, List(HOLFunction(f,_,_))) =>
            println(f)
            //println(g)
          case _ => println("no match")
        }

        red must beEqualTo(f2)
        */
        //TODO: something in the conversion is still weird, fix it

      }
    }
  }

  "Type replacement" should {
    "work for simple terms" in {
      val fterm1 = fol.Function(ConstantStringSymbol("f"), List(
        fol.FOLConst(ConstantStringSymbol("q_1")),
        fol.FOLConst(ConstantStringSymbol("c"))))

      val fterm2 = fol.AllVar(fol.FOLVar(VariableStringSymbol("x")),
                              fol.Atom(ConstantStringSymbol("P"),
                                       List(fol.FOLVar(VariableStringSymbol("q_1")),
                                            fol.FOLConst(ConstantStringSymbol("q_1"))) ))

      val hterm1 = changeTypeIn(fol2hol(fterm1), Map[String, TA](("q_1", Ti()->Ti()) ))
      val hterm2 = changeTypeIn(fol2hol(fterm2), Map[String, TA](("q_1", Ti()->Ti()) ))
      ok
    }
  }
}
