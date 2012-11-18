package at.logic.language.schema

import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.{VariableSymbolA, VariableStringSymbol}
import at.logic.language.lambda.BetaReduction._
import at.logic.language.lambda.typedLambdaCalculus.{App, Abs}
import at.logic.language.lambda.BetaReduction.ImplicitStandardStrategy._
import at.logic.language.lambda.typedLambdaCalculus._
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.language.lambda.types._
import at.logic.language.hol._
import at.logic.language.hol.Definitions._

@RunWith(classOf[JUnitRunner])
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
    val imp = Imp(neg.asInstanceOf[HOLFormula], and.asInstanceOf[HOLFormula])

    "create IndexedPredicate correctly (1)" in {
      (p1) must beLike {case f: SchemaFormula => ok}
    }
    "create IndexedPredicate correctly (2)" in {
      (pi) must beLike {case f: SchemaFormula => ok}
    }
    "create SchemaFormula correctly (1)" in {
      (and) must beLike {case f: SchemaFormula => ok}
    }
    "create SchemaFormula correctly (2)" in {
      (bigAnd) must beLike {case f: SchemaFormula => ok}
    }
    "create SchemaFormula correctly (3)" in {
      (bigOr) must beLike {case f: SchemaFormula => ok}
    }
    "create SchemaFormula correctly (4)" in {
      (imp) must beLike {case f: SchemaFormula => ok}
    }
    "correctly deal with bound variables in the BigAnd extractor (2)" in {
      val pi = IndexedPredicate(ConstantStringSymbol("p"), i::Nil)
      val f = BigAnd(i, pi, IntZero(), IntZero())
      val res = f match {
        case BigAnd(v, f, ub, lb) => Abs(v, f)
      }
      res must beEqualTo( Abs(i, pi) )
    }
    "correctly deal with bound variables in the BigAnd extractor (1)" in {
      val pi = IndexedPredicate(ConstantStringSymbol("p"), i::Nil)
      val p0 = IndexedPredicate(ConstantStringSymbol("p"), IntZero()::Nil)
      val f = BigAnd(i, pi, IntZero(), IntZero())
      val res = f match {
        case BigAnd(v, f, ub, lb) => App(Abs(v, f), ub)
      }
      betaNormalize( res ) must beEqualTo( p0 )
    }
    "perform the unapply function in BigAnd correctly" in {
       val iformula = new SchemaAbs(i.asInstanceOf[Var], p1)
       val bigConj = BigAnd(iformula, one, two)
       (BigAnd.unapply(bigConj).get._1 must beEqualTo (i)) &&
       (BigAnd.unapply(bigConj).get._2 must beEqualTo (p1)) &&
       (BigAnd.unapply(bigConj).get._3 must beEqualTo (one)) &&
       (BigAnd.unapply(bigConj).get._4 must beEqualTo (two))
    }

    "have correct BiggerThan constructor" in {
      val bt1 = BiggerThan(i, one)
      val bt2 = BiggerThan(two, one)
      val bt3 = BiggerThan(one, two)
      val bt4 = BiggerThan(two, i)
      bt1 must beLike {
        case Atom(BiggerThanSymbol, x::y::Nil) => ok
        case _ => ko
      }
    }

    "create a schematic term" in {
      val fconst = HOLConst(new ConstantStringSymbol("f"), Tindex()->Tindex()->Tindex())
      val gconst = HOLConst(new ConstantStringSymbol("g"), Tindex()->Tindex())
      val hconst = HOLConst(new ConstantStringSymbol("h"), Tindex()->Tindex())

      def g(t: HOLExpression): HOLExpression = {
        HOLApp(gconst, t)
      }

      def h(t: HOLExpression): HOLExpression = {
        HOLApp(hconst, t)
      }

      def f(n: IntegerTerm, v: HOLExpression): HOLExpression = {
        n match {
          case IntZero() => g(n)
          case _ => g(f(Pred(n), v))
        }
      }

      print("\n\nf(4,0) = ")
      println(f(Succ(Succ(Succ(Succ(IntZero())))), IntZero()))
      true must beEqualTo (true)
    }

    "unfold a schematic term" in {
      def f = HOLConst(new ConstantStringSymbol("f"), Ti()->Ti())
      def h = HOLConst(new ConstantStringSymbol("h"), ->(Tindex() , ->(Ti(), Ti())))
      def g = HOLConst(new ConstantStringSymbol("g"), ->(Tindex() , ->(Ti(), Ti())))
      val k = IntVar(new VariableStringSymbol("k"))
      val x = foVar("x")
      val z = indexedFOVar(new VariableStringSymbol("z"), Succ(IntZero()))
      val z0 = indexedFOVar(new VariableStringSymbol("z"), IntZero())
      val base = x
      val step = foTerm("f",  sTerm(g, Succ(k), x::Nil)::Nil)
      dbTRS.clear
      dbTRS.add(g, base, step)
      val term = sTerm(g, Succ(Succ(k)), x::Nil)
      val term1 = sTerm(g, Succ(IntZero()), z::Nil)
      val term2 = sTerm(g, IntZero(), z0::Nil)

      val unf = unfoldSTerm(term2)
      println("\n\nterm = "+term2)
      println("unfold = "+unf)
      println()
      true must beEqualTo (true)
      
    }


  }
}
