/** 
 * Description: 
**/

package at.logic.algorithms.lk.simplification

import _root_.at.logic.language.fol.{FOLFormula, FOLExpression}
import at.logic.parsing.language.simple.{SimpleFOLParser, SimpleHOLParser}
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner

import at.logic.language.hol._
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.types._
import at.logic.calculi.lk.base.Sequent
import at.logic.parsing.readers.StringReader
import at.logic.calculi.lk.base.types._

private class MyParser(input: String) extends StringReader(input) with SimpleHOLParser
private class MyParserF(input: String) extends StringReader(input) with SimpleFOLParser

@RunWith(classOf[JUnitRunner])
class SimplificationTest extends SpecificationWithJUnit {
  "Simplifications" should {
      val a = HOLVarFormula( "a" )
      val b = HOLVarFormula( "b" )
      val s1 = new FSequent( a::Nil, a::Nil )
      val s2 = new FSequent( b::a::b::Nil, b::b::b::a::b::Nil )
      val s3 = new FSequent( a::Nil, b::Nil )
      val s4 = new FSequent( b::Nil, a::Nil )
      
      val f1a = new MyParser("And P(z:(i->i)) Q(b:(i->i))").getTerm().asInstanceOf[HOLFormula]
      val f2a = new MyParser("And P(f(x:i, y:i, a:i):(i->i), z:(i->i)) Q(Neg T(x:i, a:i, b:(i->i), g(x:i):i), Forall x1: (i -> (i -> i)) a(x1: (i -> (i -> i)), x: i, c1: (i -> i)))").getTerm().asInstanceOf[HOLFormula]
      // the bs are variants of the as
      val f1b = new MyParser("And P(z2:(i->i)) Q(b:(i->i))").getTerm().asInstanceOf[HOLFormula]
      val f2b = new MyParser("And P(f(x2:i, y:i, a:i):(i->i), z2:(i->i)) Q(Neg T(x2:i, a:i, b:(i->i), g(x2:i):i), Forall x1: (i -> (i -> i)) a(x1: (i -> (i -> i)), x2: i, c1: (i -> i)))").getTerm().asInstanceOf[HOLFormula]
      // the cs are not variants of the others
      val f1c = new MyParser("And P(z2:(i->i)) Q(b:(i->i))").getTerm().asInstanceOf[HOLFormula]
      val f2c = new MyParser("And P(f(x:i, y:i, a:i):(i->i), z1:(i->i)) Q(Neg T(x:i, a:i, b:(i->i), g(x:i):i), Forall x1: (i -> (i -> i)) a(x1: (i -> (i -> i)), x: i, c1: (i -> i)))").getTerm().asInstanceOf[HOLFormula]
      // the ds are alpha-equivalent to the as and should be removed as well
      val f1d = new MyParser("And P(z:(i->i)) Q(b:(i->i))").getTerm().asInstanceOf[HOLFormula]
      val f2d = new MyParser("And P(f(x:i, y:i, a:i):(i->i), z:(i->i)) Q(Neg T(x:i, a:i, b:(i->i), g(x:i):i), Forall x2: (i -> (i -> i)) a(x2: (i -> (i -> i)), x: i, c1: (i -> i)))").getTerm().asInstanceOf[HOLFormula]

      val s5 = new FSequent( f1a::Nil, f2a::Nil )
      val s6 = new FSequent( f1b::Nil, f2b::Nil )
      val s7 = new FSequent( f1c::Nil, f2c::Nil )
      val s8 = new FSequent( f1d::Nil, f2d::Nil )
      
      val a1 = new MyParser("P(x:i)").getTerm().asInstanceOf[HOLFormula]
      val a2 = new MyParser("P(f(x:i,y:i):i)").getTerm().asInstanceOf[HOLFormula]
      val a3 = new MyParser("P(a:i)").getTerm().asInstanceOf[HOLFormula]
      val a4 = new MyParser("P(b:i)").getTerm().asInstanceOf[HOLFormula]
      val a5 = new MyParser("P(f(b:i,a:i):i)").getTerm().asInstanceOf[HOLFormula]
      
      val f1 = Atom(ConstantStringSymbol("<"), HOLConst(ConstantStringSymbol("1"), Ti())::Atom(ConstantStringSymbol("p"), HOLVar(VariableStringSymbol("x"), Ti())::Nil)::Nil)
      val f2 = Atom(ConstantStringSymbol("="), HOLVar(VariableStringSymbol("x"), Ti())::(HOLConst(ConstantStringSymbol("s"), Ti())::Nil))

      val seq1 = new FSequent(Nil, f1::Nil)
      val seq2 = new FSequent(f2::Nil, f1::Nil)

      val s9 = new FSequent(Nil, a1::a2::Nil)
      val s10 = new FSequent(f1a::f1b::Nil, a3::a4::a5::Nil)

      val f3 = Atom(ConstantStringSymbol("="), HOLConst(ConstantStringSymbol("1"), Ti())::(HOLConst(ConstantStringSymbol("1"), Ti())::Nil))
      val f4 = Atom(ConstantStringSymbol("="), HOLVar(VariableStringSymbol("x"), Ti())::(HOLVar(VariableStringSymbol("x"), Ti())::Nil))
      val f5 = Atom(ConstantStringSymbol("="), HOLVar(VariableStringSymbol("x"), Ti())::(HOLConst(ConstantStringSymbol("1"), Ti())::Nil))

      val seq3 = new FSequent(Nil, f3::Nil)
      val seq4 = new FSequent(Nil, f4::f5::Nil)

    "correctly delete tautologous sequents" in {
      val list = s1::s2::s3::s4::s1::Nil
      val dlist = deleteTautologies( list )
      dlist.size must beEqualTo( 2 )
    }

    "correctly set-normalize a list of Sequents" in {
      val list = s1::s2::s2::s1::s2::s3::s1::s2::s4::s3::s2::s1::s2::s3::Nil
      val set = setNormalize( list )
      set.size must beEqualTo( 4 )
    }

    "correctly remove variants from a set of Sequents" in {
      val ls = List(s5,s6,s7,s8)
      val ret = variantsRemoval( ls )
      ret.size must beEqualTo( 2 )
    }

    "correctly remove subsumed sequents from a set of Sequents" in {
      implicit def term2formula(x: HOLExpression): HOLFormula = x.asInstanceOf[HOLFormula]
      implicit def listterm2listformula(x: List[HOLFormula]): List[HOLFormula] = x.map(y => y.asInstanceOf[HOLFormula])
      implicit def formula2list(x: HOLFormula): List[HOLFormula] = List(x)
      implicit def term2list(x: HOLExpression): List[HOLFormula] = List(x.asInstanceOf[HOLFormula])

      val f1 = new MyParserF("<(a, p(x))").getTerm()
      val f2 = new MyParserF("=(x,s)").getTerm()
      val f3 = new MyParserF("=(a,a)").getTerm()
      val f4 = new MyParserF("=(x,x)").getTerm()
      val f5 = new MyParserF("=(x,a)").getTerm()
      
      val seq1f = new FSequent(Nil, f1::Nil)
      val seq2f = new FSequent(f2::Nil, f1::Nil)
      val seq3f = new FSequent(Nil, f3::Nil)
      val seq4f = new FSequent(Nil, f4.asInstanceOf[HOLFormula]::f5.asInstanceOf[HOLFormula]::Nil)

      "FOL" in {
        "1" in {
          val ls = List(s9,s10)
          val ret = subsumedClausesRemovalHOL( ls )
          ret.size must beEqualTo( 1 )
        }
        "2" in {
          val ls = List(seq1f,seq2f,seq3f,seq4f)
          val ret = subsumedClausesRemoval( ls )
          ret.toSet must beEqualTo( Set(seq1f,seq4f) )
        }
      }
      "HOL" in {
       "1" in {
          val ls = List(s9,s10)
          val ret = subsumedClausesRemovalHOL( ls )
          ret.size must beEqualTo( 1 )
        }
        "2" in {
          val ls = List(seq1f,seq2f,seq3f,seq4f)
          val ret = subsumedClausesRemovalHOL( ls )
          ret.toSet must beEqualTo( Set(seq1f,seq4f) )
        }
      }
    }
  }
}
