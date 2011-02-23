package at.logic.language.schema

import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.hol.Atom
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
    val pi = IndexedPredicate(p, i::Nil)
    val p1 = IndexedPredicate(p, one::Nil)
    val p2 = IndexedPredicate(p, two::Nil)
    val bigAnd = BigAnd(new SchemaAbs(i, pi), one, two)
    val bigOr = BigOr(i, pi, one, two)
    val and = And(p1, p2)
    val or = Or(bigAnd, bigOr)
    val neg = Neg(or)
    val imp = Imp(neg, and)


    "create IndexedPredicate correctly (1)" in {
      (p1) must beLike {case f: SchemaFormula => true}
    }
    "create IndexedPredicate correctly (2)" in {
      (pi) must beLike {case f: SchemaFormula => true}
    }
    "create SchemaFormula correctly (1)" in {
      (and) must beLike {case f: SchemaFormula => true}
    }
    "create SchemaFormula correctly (2)" in {
      (bigAnd) must beLike {case f: SchemaFormula => true}
    }
    "create SchemaFormula correctly (3)" in {
      (bigOr) must beLike {case f: SchemaFormula => true}
    }
    "create SchemaFormula correctly (4)" in {
      (imp) must beLike {case f: SchemaFormula => true}
    }
    "correctly deal with bound variables in the BigAnd extractor (2)" in {
      val pi = IndexedPredicate(ConstantStringSymbol("p"), i::Nil)
      val f = BigAnd(i, pi, IntZero(), IntZero())
      val res = f match {
        case BigAnd(v, f, ub, lb) => Abs(v, f)
      }
      res must beEqual( Abs(i, pi) )
    }
    "correctly deal with bound variables in the BigAnd extractor (1)" in {
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
    "have correct BiggerThan constructor" in {
      val bt1 = BiggerThan(i, one)
      val bt2 = BiggerThan(two, one)
      val bt3 = BiggerThan(one, two)
      val bt4 = BiggerThan(two, i)
      bt1 must beLike {
        case Atom(BiggerThanSymbol, x::y::Nil) => true
        case _ => false
      }
    }
  }
}
