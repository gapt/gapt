/** 
 * Description: 
**/

package at.logic.algorithms.lk.simplification

import org.specs._
import org.specs.runner._
import org.specs.matcher.Matcher

import at.logic.language.hol.propositions._
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.types._
import at.logic.calculi.lk.base.Sequent
import scala.collection.immutable.EmptySet
import at.logic.parsing.readers.StringReader
import at.logic.parsing.language.simple.SimpleHOLParser

private class MyParser(input: String) extends StringReader(input) with SimpleHOLParser

class SimplificationTest extends SpecificationWithJUnit {
  "Simplifications" should {
      val a = HOLVarFormula( "a" )
      val b = HOLVarFormula( "b" )
      val s1 = Sequent( a::Nil, a::Nil )
      val s2 = Sequent( b::a::b::Nil, b::b::b::a::b::Nil )
      val s3 = Sequent( a::Nil, b::Nil )
      val s4 = Sequent( b::Nil, a::Nil )
      
      val f1a = new MyParser("And P(z:(i->i)) Q(b:(i->i))").getTerm().asInstanceOf[Formula]
      val f2a = new MyParser("And P(f(x:i, y:i, a:i):(i->i), z:(i->i)) Q(Neg T(x:i, a:i, b:(i->i), g(x:i):i), Forall x1: (i -> (i -> i)) a(x1: (i -> (i -> i)), x: i, c1: (i -> i)))").getTerm().asInstanceOf[Formula]
      // the bs are variants of the as
      val f1b = new MyParser("And P(z2:(i->i)) Q(b:(i->i))").getTerm().asInstanceOf[Formula]
      val f2b = new MyParser("And P(f(x2:i, y:i, a:i):(i->i), z2:(i->i)) Q(Neg T(x2:i, a:i, b:(i->i), g(x2:i):i), Forall x1: (i -> (i -> i)) a(x1: (i -> (i -> i)), x2: i, c1: (i -> i)))").getTerm().asInstanceOf[Formula]
      // the cs are not variants of the others
      val f1c = new MyParser("And P(z2:(i->i)) Q(b:(i->i))").getTerm().asInstanceOf[Formula]
      val f2c = new MyParser("And P(f(x:i, y:i, a:i):(i->i), z1:(i->i)) Q(Neg T(x:i, a:i, b:(i->i), g(x:i):i), Forall x1: (i -> (i -> i)) a(x1: (i -> (i -> i)), x: i, c1: (i -> i)))").getTerm().asInstanceOf[Formula]
      // the ds are alpha-equivalent to the as and should be removed as well
      val f1d = new MyParser("And P(z:(i->i)) Q(b:(i->i))").getTerm().asInstanceOf[Formula]
      val f2d = new MyParser("And P(f(x:i, y:i, a:i):(i->i), z:(i->i)) Q(Neg T(x:i, a:i, b:(i->i), g(x:i):i), Forall x2: (i -> (i -> i)) a(x2: (i -> (i -> i)), x: i, c1: (i -> i)))").getTerm().asInstanceOf[Formula]

      val s5 = Sequent( f1a::Nil, f2a::Nil )
      val s6 = Sequent( f1b::Nil, f2b::Nil )
      val s7 = Sequent( f1c::Nil, f2c::Nil )
      val s8 = Sequent( f1d::Nil, f2d::Nil )
      
      val a1 = new MyParser("P(x:i)").getTerm().asInstanceOf[Formula]
      val a2 = new MyParser("P(f(x:i,y:i):i)").getTerm().asInstanceOf[Formula]
      val a3 = new MyParser("P(a:i)").getTerm().asInstanceOf[Formula]
      val a4 = new MyParser("P(b:i)").getTerm().asInstanceOf[Formula]
      val a5 = new MyParser("P(f(b:i,a:i):i)").getTerm().asInstanceOf[Formula]
      
      val seq1 = Sequent(Nil, Atom(ConstantStringSymbol("<"), HOLConst(ConstantStringSymbol("1"), Ti())::Atom(ConstantStringSymbol("p"), HOLVar(VariableStringSymbol("x"), Ti())::Nil)::Nil)::Nil)
      val seq2 = Sequent(Atom(ConstantStringSymbol("="), HOLVar(VariableStringSymbol("x"), Ti())::(HOLConst(ConstantStringSymbol("s"), Ti())::Nil))::Nil, Atom(ConstantStringSymbol("<"), HOLConst(ConstantStringSymbol("1"), Ti())::Atom(ConstantStringSymbol("p"), HOLVar(VariableStringSymbol("x"), Ti())::Nil)::Nil)::Nil)

      val s9 = Sequent(Nil, a1::a2::Nil)
      val s10 = Sequent(f1a::f1b::Nil, a3::a4::a5::Nil)

      val seq3 = Sequent(Nil, Atom(ConstantStringSymbol("="), HOLConst(ConstantStringSymbol("1"), Ti())::(HOLConst(ConstantStringSymbol("1"), Ti())::Nil))::Nil)
      val seq4 = Sequent(Nil, Atom(ConstantStringSymbol("="), HOLVar(VariableStringSymbol("x"), Ti())::(HOLVar(VariableStringSymbol("x"), Ti())::Nil))::Atom(ConstantStringSymbol("="), HOLVar(VariableStringSymbol("x"), Ti())::(HOLConst(ConstantStringSymbol("1"), Ti())::Nil))::Nil)

    "correctly delete tautologous sequents" in {
      val list = s1::s2::s3::s4::s1::Nil
      val dlist = deleteTautologies( list )
      dlist.size must beEqual( 2 )
    }

    "correctly set-normalize a list of Sequents" in {
      val list = s1::s2::s2::s1::s2::s3::s1::s2::s4::s3::s2::s1::s2::s3::Nil
      val set = setNormalize( list )
      set.size must beEqual( 4 )
    }

    "correctly remove variants from a set of Sequents" in {
      val ls = List(s5,s6,s7,s8)
      val ret = variantsRemoval( ls )
      ret.size must beEqual( 2 )
    }

    "correctly remove subsumed sequents from a set of Sequents" in {
      "1" in {
        val ls = List(s9,s10)
        val ret = subsumedClausesRemoval( ls )
        ret.size must beEqual( 1 )
      }
      "2" in {
        val ls = List(seq1,seq2,seq3,seq4)
        val ret = subsumedClausesRemoval( ls )
        ret.size must beEqual( 2 )
      }
    }
  }
}
