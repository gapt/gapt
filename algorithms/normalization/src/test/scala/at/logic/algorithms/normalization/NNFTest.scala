package at.logic.algorithms.normalization

import org.specs2.mutable._
import at.logic.language.hol._
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.types._
import at.logic.parsing.readers.StringReader
import at.logic.parsing.language.simple.SimpleHOLParser
import scala.collection.mutable.Map
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.language.lambda.symbols.VariableStringSymbol

@RunWith(classOf[JUnitRunner])
class NNFTest extends SpecificationWithJUnit {
  val f1a = new MyParser("And P(z:(i->i)) Q(b:(i->i))").getTerm().asInstanceOf[Formula]
  val f1b = new MyParser("And P(x_{1}:(i->i)) Q(b:(i->i))").getTerm().asInstanceOf[Formula]
  val f2a = new MyParser("And P(f(x:i, y:i, a:i):(i->i), z:(i->i)) Q(Neg T(x:i, a:i, b:(i->i), g(x:i):i), Forall x1: (i -> (i -> i)) a(x1: (i -> (i -> i)), x: i, c1: (i -> i)))").getTerm().asInstanceOf[Formula]
  val f2b = new MyParser("And P(f(x_{1}:i, x_{2}:i, a:i):(i->i), x_{3}:(i->i)) Q(Neg T(x_{1}:i, a:i, b:(i->i), g(x_{1}:i):i), Forall x_{4}: (i -> (i -> i)) a(x_{4}: (i -> (i -> i)), x_{1}: i, c1: (i -> i)))").getTerm().asInstanceOf[Formula]

  "NNF" should {
    "transform to NNF the formulas" in {
      "1" in {
        val P = HOLVar(new VariableStringSymbol("P"), Ti() -> To())
        val a = HOLConst(new ConstantStringSymbol("a"), Ti())
        val Pa = Atom(P, a::Nil)
        val f = Neg(Neg(Pa))
        Pa must beEqualTo(NNF(f))
      }
      "2" in {
        val P = HOLVar(new VariableStringSymbol("P"), Ti() -> To())
        val a = HOLConst(new ConstantStringSymbol("a"), Ti())
        val Pa = Atom(P, a::Nil)
        val f = Neg(And(Neg(Pa), Pa))
        NNF(f) must beEqualTo(Or(Pa, Neg(Pa)))
      }
      "3" in {
        val P = HOLVar(new VariableStringSymbol("P"), Ti() -> To())
        val a = HOLConst(new ConstantStringSymbol("a"), Ti())
        val Pa = Atom(P, a::Nil)
        val f = Neg(And(Neg(Pa), Neg(Pa)))
        NNF(f) must beEqualTo(Or(Pa, Pa))
      }
      "4" in {
        val P = HOLVar(new VariableStringSymbol("P"), Ti() -> To())
        val a = HOLConst(new ConstantStringSymbol("a"), Ti())
        val Pa = Atom(P, a::Nil)
        val f = Or(Neg(And(Neg(Pa), Neg(Pa))), Neg(Pa))
        NNF(f) must beEqualTo(Or(Or(Pa, Pa), Neg(Pa)))
      }
      "5" in {
        val P = HOLVar(new VariableStringSymbol("P"), Ti() -> To())
        val a = HOLConst(new ConstantStringSymbol("a"), Ti())
        val Pa = Atom(P, a::Nil)
        val f = And(Neg(And(Neg(Pa), Neg(Pa))), Neg(Neg(Pa)))
        NNF(f) must beEqualTo(And(Or(Pa, Pa), Pa))
      }
      "6" in {
        val P = HOLVar(new VariableStringSymbol("P"), Ti() -> To())
        val a = HOLConst(new ConstantStringSymbol("a"), Ti())
        val Pa = Atom(P, a::Nil)
        val f = Neg(And(Neg(And(Neg(Pa), Neg(Pa))), Neg(Neg(Pa))))
        NNF(f) must beEqualTo(Or(And(Neg(Pa), Neg(Pa)), Neg(Pa)))
      }
      "7" in {
        val P = HOLVar(new VariableStringSymbol("P"), Ti() -> To())
        val a = HOLConst(new ConstantStringSymbol("a"), Ti())
        val Pa = Atom(P, a::Nil)
        val f = Neg(And(Neg(And(Neg(Neg(Pa)), Neg(Pa))), Neg(Neg(Pa))))
        NNF(f) must beEqualTo(Or(And(Pa, Neg(Pa)), Neg(Pa)))
      }
      "8" in {
        val P = HOLVar(new VariableStringSymbol("P"), Ti() -> To())
        val a = HOLConst(new ConstantStringSymbol("a"), Ti())
        val Pa = Atom(P, a::Nil)
        val f = Neg(And(Neg(And(Neg(Neg(Pa)), Neg(Pa))), Neg(Imp(Neg(Pa), Pa))))
        NNF(f) must beEqualTo(Or(And(Pa, Neg(Pa)), Or(Pa, Pa)))        
      }
      "9" in {
        val P = HOLVar(new VariableStringSymbol("P"), Ti() -> To())
        val a = HOLConst(new ConstantStringSymbol("a"), Ti())
        val Pa = Atom(P, a::Nil)
        val f = Neg(Neg(And(Neg(And(Neg(Neg(Pa)), Neg(Pa))), Neg(Imp(Neg(Pa), Pa)))))
        NNF(f) must beEqualTo(And(Or(Neg(Pa), Pa), And(Neg(Pa), Neg(Pa))))
      }
      "10" in {
        val P = HOLVar(new VariableStringSymbol("P"), Ti() -> To())
        val a = HOLConst(new ConstantStringSymbol("a"), Ti())
        val Pa = Atom(P, a::Nil)
        val f = Imp(Neg(Neg(And(Neg(And(Neg(Neg(Pa)), Neg(Pa))), Neg(Imp(Neg(Pa), Pa))))), Pa)
        NNF(f) must beEqualTo(Or(Or( And(Pa, Neg(Pa)) , Or(Pa, Pa) ) , Pa))
//        println("\nNNF( "+f+" ) = "+NNF(f))
//        ok
      }
    }
  }
}
