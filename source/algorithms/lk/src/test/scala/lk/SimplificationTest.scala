/** 
 * Description: 
**/

package at.logic.algorithms.lk.simplification

import _root_.at.logic.language.fol.{FOLFormula, FOLExpression}
import at.logic.parsing.language.simple.{SimpleFOLParser, SimpleHOLParser}
import org.specs._
import org.specs.runner._
import org.specs.matcher.Matcher

import at.logic.language.hol._
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.types._
import at.logic.calculi.lk.base.Sequent
import at.logic.parsing.readers.StringReader
import at.logic.calculi.occurrences._

private class MyParser(input: String) extends StringReader(input) with SimpleHOLParser
private class MyParserF(input: String) extends StringReader(input) with SimpleFOLParser

class SimplificationTest extends SpecificationWithJUnit {
  "Simplifications" should {
      val a = HOLVarFormula( "a" )
      val b = HOLVarFormula( "b" )
      val a_occ = defaultFormulaOccurrenceFactory.createFormulaOccurrence(a, Nil)
      val b_occ = defaultFormulaOccurrenceFactory.createFormulaOccurrence(a, Nil)
      val s1 = Sequent( a_occ::Nil, a_occ::Nil )
      val s2 = Sequent( b_occ::a_occ::b_occ::Nil, b_occ::b_occ::b_occ::a_occ::b_occ::Nil )
      val s3 = Sequent( a_occ::Nil, b_occ::Nil )
      val s4 = Sequent( b_occ::Nil, a_occ::Nil )
      
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

      val f1a_occ = defaultFormulaOccurrenceFactory.createFormulaOccurrence(f1a, Nil)
      val f2a_occ = defaultFormulaOccurrenceFactory.createFormulaOccurrence(f2a, Nil)
      val f1b_occ = defaultFormulaOccurrenceFactory.createFormulaOccurrence(f1b, Nil)
      val f2b_occ = defaultFormulaOccurrenceFactory.createFormulaOccurrence(f2b, Nil)
      val f1c_occ = defaultFormulaOccurrenceFactory.createFormulaOccurrence(f1c, Nil)
      val f2c_occ = defaultFormulaOccurrenceFactory.createFormulaOccurrence(f2c, Nil)
      val f1d_occ = defaultFormulaOccurrenceFactory.createFormulaOccurrence(f1d, Nil)
      val f2d_occ = defaultFormulaOccurrenceFactory.createFormulaOccurrence(f2d, Nil)


      val s5 = Sequent( f1a_occ::Nil, f2a_occ::Nil )
      val s6 = Sequent( f1b_occ::Nil, f2b_occ::Nil )
      val s7 = Sequent( f1c_occ::Nil, f2c_occ::Nil )
      val s8 = Sequent( f1d_occ::Nil, f2d_occ::Nil )
      
      val a1 = new MyParser("P(x:i)").getTerm().asInstanceOf[HOLFormula]
      val a2 = new MyParser("P(f(x:i,y:i):i)").getTerm().asInstanceOf[HOLFormula]
      val a3 = new MyParser("P(a:i)").getTerm().asInstanceOf[HOLFormula]
      val a4 = new MyParser("P(b:i)").getTerm().asInstanceOf[HOLFormula]
      val a5 = new MyParser("P(f(b:i,a:i):i)").getTerm().asInstanceOf[HOLFormula]
      
      val a1_occ = defaultFormulaOccurrenceFactory.createFormulaOccurrence(a1, Nil)
      val a2_occ = defaultFormulaOccurrenceFactory.createFormulaOccurrence(a2, Nil)
      val a3_occ = defaultFormulaOccurrenceFactory.createFormulaOccurrence(a3, Nil)
      val a4_occ = defaultFormulaOccurrenceFactory.createFormulaOccurrence(a4, Nil)
      val a5_occ = defaultFormulaOccurrenceFactory.createFormulaOccurrence(a5, Nil)

      val f1 = Atom(ConstantStringSymbol("<"), HOLConst(ConstantStringSymbol("1"), Ti())::Atom(ConstantStringSymbol("p"), HOLVar(VariableStringSymbol("x"), Ti())::Nil)::Nil)
      val f2 = Atom(ConstantStringSymbol("="), HOLVar(VariableStringSymbol("x"), Ti())::(HOLConst(ConstantStringSymbol("s"), Ti())::Nil))

      val f1_occ = defaultFormulaOccurrenceFactory.createFormulaOccurrence(f1, Nil)
      val f2_occ = defaultFormulaOccurrenceFactory.createFormulaOccurrence(f2, Nil)

      val seq1 = Sequent(Nil, f1_occ::Nil)
      val seq2 = Sequent(f2_occ::Nil, f1_occ::Nil)

      val s9 = Sequent(Nil, a1_occ::a2_occ::Nil)
      val s10 = Sequent(f1a_occ::f1b_occ::Nil, a3_occ::a4_occ::a5_occ::Nil)

      val f3 = Atom(ConstantStringSymbol("="), HOLConst(ConstantStringSymbol("1"), Ti())::(HOLConst(ConstantStringSymbol("1"), Ti())::Nil))
      val f4 = Atom(ConstantStringSymbol("="), HOLVar(VariableStringSymbol("x"), Ti())::(HOLVar(VariableStringSymbol("x"), Ti())::Nil))
      val f5 = Atom(ConstantStringSymbol("="), HOLVar(VariableStringSymbol("x"), Ti())::(HOLConst(ConstantStringSymbol("1"), Ti())::Nil))

      val f3_occ = defaultFormulaOccurrenceFactory.createFormulaOccurrence(f3, Nil)
      val f4_occ = defaultFormulaOccurrenceFactory.createFormulaOccurrence(f4, Nil)
      val f5_occ = defaultFormulaOccurrenceFactory.createFormulaOccurrence(f5, Nil)

      val seq3 = Sequent(Nil, f3_occ::Nil)
      val seq4 = Sequent(Nil, f4_occ::f5_occ::Nil)

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
      implicit def term2formula(x: HOLExpression): HOLFormula = x.asInstanceOf[HOLFormula]
      implicit def listterm2listformula(x: List[HOLFormula]): List[HOLFormula] = x.map(y => y.asInstanceOf[HOLFormula])
      implicit def formula2list(x: HOLFormula): List[HOLFormula] = List(x)
      implicit def term2list(x: HOLExpression): List[HOLFormula] = List(x.asInstanceOf[HOLFormula])

      val f1 = new MyParserF("<(a, p(x))").getTerm()
      val f2 = new MyParserF("=(x,s)").getTerm()
      val f3 = new MyParserF("=(a,a)").getTerm()
      val f4 = new MyParserF("=(x,x)").getTerm()
      val f5 = new MyParserF("=(x,a)").getTerm()
      
      val f1_occ = defaultFormulaOccurrenceFactory.createFormulaOccurrence(f1, Nil)
      val f2_occ = defaultFormulaOccurrenceFactory.createFormulaOccurrence(f2, Nil)
      val f3_occ = defaultFormulaOccurrenceFactory.createFormulaOccurrence(f3, Nil)
      val f4_occ = defaultFormulaOccurrenceFactory.createFormulaOccurrence(f4, Nil)
      val f5_occ = defaultFormulaOccurrenceFactory.createFormulaOccurrence(f5, Nil)

      val seq1f = Sequent(Nil, f1_occ::Nil)
      val seq2f = Sequent(f2_occ::Nil, f1_occ::Nil)
      val seq3f = Sequent(Nil, f3_occ::Nil)
      val seq4f = Sequent(Nil, f4_occ::f5_occ::Nil)

      "FOL" in {
        "1" in {
          val ls = List(s9,s10)
          val ret = subsumedClausesRemovalHOL( ls )
          ret.size must beEqual( 1 )
        }
        "2" in {
          val ls = List(seq1f,seq2f,seq3f,seq4f)
          val ret = subsumedClausesRemoval( ls )
          ret.toSet must beEqual( Set(seq1f,seq4f) )
        }
      }
      "HOL" in {
       "1" in {
          val ls = List(s9,s10)
          val ret = subsumedClausesRemovalHOL( ls )
          ret.size must beEqual( 1 )
        }
        "2" in {
          val ls = List(seq1f,seq2f,seq3f,seq4f)
          val ret = subsumedClausesRemovalHOL( ls )
          ret.toSet must beEqual( Set(seq1f,seq4f) )
        }
      }
    }
  }
}
