package at.logic.language.schema

import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.{VariableSymbolA, VariableStringSymbol}
import at.logic.language.lambda.BetaReduction._
import at.logic.language.lambda.typedLambdaCalculus.{App, Abs}
import at.logic.language.lambda.BetaReduction.ImplicitStandardStrategy._
import at.logic.language.lambda.typedLambdaCalculus._
import org.specs.SpecificationWithJUnit

class SchemaTest extends SpecificationWithJUnit {
  "Schema" should {
    val i = IntVar(new VariableStringSymbol("i"))
    val one = Succ(IntZero())
    val two = Succ(Succ(IntZero()))
    val p = new ConstantStringSymbol("P")
    val p1 = IndexedPredicate(p, one::Nil)
    val p2 = IndexedPredicate(p, two::Nil)

    "create IndexedPredicate correctly (1)" in {
      (p1) must beLike {case f: SchemaFormula => true}
    }
    "create IndexedPredicate correctly (2)" in {
      (p2) must beLike {case f: SchemaFormula => true}
    }

    "create SchemaFormula correctly" in {
      val and = And(p1, p2)
      (and) must beLike {case f: SchemaFormula => true}
    }
    "correctly deal with bound variables in the BigAnd extractor (2)" in {
      val i = IntVar(new VariableStringSymbol("i"))
      val pi = IndexedPredicate(ConstantStringSymbol("p"), i::Nil)
      val f = BigAnd(i, pi, IntZero(), IntZero())
      val res = f match {
        case BigAnd(v, f, ub, lb) => Abs(v, f)
      }
      res must beEqual( Abs(i, pi) )
    }
    "correctly deal with bound variables in the BigAnd extractor (1)" in {
      val i = IntVar(new VariableStringSymbol("i"))
      val pi = IndexedPredicate(ConstantStringSymbol("p"), i::Nil)
      val p0 = IndexedPredicate(ConstantStringSymbol("p"), IntZero()::Nil)
      val f = BigAnd(i, pi, IntZero(), IntZero())
      val res = f match {
        case BigAnd(v, f, ub, lb) => App(Abs(v, f), ub)
      }
      betaNormalize( res ) must beEqual( p0 )
    }

    "perform the unapply function in BigAnd correctly" in {
       val iformula = new SchemaAbs(i.asInstanceOf[Var], p1)
       val bigConj = BigAnd(iformula, one, two)
       (BigAnd.unapply(bigConj).get._1 must beEqual (i)) &&
       (BigAnd.unapply(bigConj).get._2 must beEqual (p1)) &&
       (BigAnd.unapply(bigConj).get._3 must beEqual (one)) &&
       (BigAnd.unapply(bigConj).get._4 must beEqual (two))
    }
  }
}
