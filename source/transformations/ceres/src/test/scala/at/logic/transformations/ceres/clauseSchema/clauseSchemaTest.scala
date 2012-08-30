package at.logic.transformations.ceres.clauseSchema

import at.logic.calculi.lk.base.FSequent
import at.logic.calculi.lk.propositionalRules.{Axiom, NegLeftRule}
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.typedLambdaCalculus.Var
import at.logic.algorithms.shlk._
import java.io.File.separator
import scala.io._
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import org.specs2.execute.Success
import at.logic.language.lambda.types._
import at.logic.language.hol._

@RunWith(classOf[JUnitRunner])
class clauseSchemaTest extends SpecificationWithJUnit {
  implicit val factory = defaultFormulaOccurrenceFactory
  import at.logic.language.schema._
  "clauseSchemaTest" should {
    "create a correct schema clause" in {
      println(Console.RED+"\n\n       clauseSchemaTest\n\n"+Console.RESET)
      val k = IntVar(new VariableStringSymbol("k"))
      val n1 = Succ(k); val n2 = Succ(n1); val n3 = Succ(n2)
      val k1 = Succ(k); val k2 = Succ(n1); val k3 = Succ(n2)
      val zero = IntZero(); val one = Succ(IntZero()); val two = Succ(Succ(IntZero())); val three = Succ(Succ(Succ(IntZero())))
      val four = Succ(three);val five = Succ(four); val six = Succ(Succ(four));val seven = Succ(Succ(five));       val A0 = IndexedPredicate(new ConstantStringSymbol("A"), IntZero())

      val Pk = IndexedPredicate(new ConstantStringSymbol("P"), k)
      val P0 = IndexedPredicate(new ConstantStringSymbol("P"), IntZero())
      val Q0 = IndexedPredicate(new ConstantStringSymbol("Q"), IntZero())
      val Pk1 = IndexedPredicate(new ConstantStringSymbol("P"), Succ(k))
      val c0 = nonVarSclause(List.empty[HOLFormula], P0::Nil)
      val ck1 = nonVarSclause(List.empty[HOLFormula], Pk1::Nil)
      val X = sClauseVar("X")
      val base: sClause = sClauseComposition(c0, X)
      val rec: sClause = sClauseComposition(ck1, X)
      val clause_schema = ClauseSchema(base, rec)
      println(base)
      println(rec)
      val non = nonVarSclause(Q0::Nil, List.empty[HOLFormula])
      val map = Map[sClauseVar, sClause]() + Pair(X.asInstanceOf[sClauseVar], non)
      val l = Ti()::To()::Tindex()::Nil
      l.foldLeft(To().asInstanceOf[TA])((x,t) => ->(x, t))
      println("l = "+l)
//      val rez = clause_schema(two, map)
//      println("\nrez = "+rez)
      println("\n\n\n")
//      println(normalizeSClause(sClauseComposition(rez, X)))
//      println(Pred(two))
      println("\n\n\n\n")
      ok
    }


    "create a fist-order schema clause" in {
      println(Console.RED+"\n\n       clauseSchemaTest\n\n"+Console.RESET)
      val k = IntVar(new VariableStringSymbol("k"))
      val i = IntVar(new VariableStringSymbol("i"))
      val l = IntVar(new VariableStringSymbol("l"))
      val n1 = Succ(k); val n2 = Succ(n1); val n3 = Succ(n2)
      val k1 = Succ(k); val k2 = Succ(n1); val k3 = Succ(n2)
      val zero = IntZero(); val one = Succ(IntZero()); val two = Succ(Succ(IntZero())); val three = Succ(Succ(Succ(IntZero())))
      val four = Succ(three);val five = Succ(four); val six = Succ(Succ(four));val seven = Succ(Succ(five));       val A0 = IndexedPredicate(new ConstantStringSymbol("A"), IntZero())

      val P0 = IndexedPredicate(new ConstantStringSymbol("P"), IntZero())
      val Q0 = IndexedPredicate(new ConstantStringSymbol("Q"), IntZero())
      val Pk1 = IndexedPredicate(new ConstantStringSymbol("P"), Succ(k))
      val c0 = nonVarSclause(List.empty[HOLFormula], P0::Nil)
      val ck1 = nonVarSclause(List.empty[HOLFormula], Pk1::Nil)
      val X = sClauseVar("X")
      val x = HOLVar(new VariableStringSymbol("x"), ->(Tindex(), Ti()))
      val y = HOLVar(new VariableStringSymbol("x"), Ti())

      val g = HOLConst(new ConstantStringSymbol("g"), ->(Ti(),Ti()))
      val st = sTermN("sigma", k::x::l::Nil)
      val sigma_base = sTermN("sigma", zero::x::l::Nil)
      val sigma_rec = sTermN("sigma", Succ(k)::x::l::Nil)
      val rewrite_base = HOLApp(x, l)
      val rewrite_step = HOLApp(g, st)
      val base: sClause = sClauseComposition(c0, X)
      val rec: sClause = sClauseComposition(ck1, X)
      val clause_schema = ClauseSchema(base, rec)
      println(rewrite_base)
      println(rewrite_step)
      val non = nonVarSclause(Q0::Nil, List.empty[HOLFormula])
      val map = Map[sClauseVar, sClause]() + Pair(X.asInstanceOf[sClauseVar], non)

      val rez = clause_schema(two, map)
      println("\nrez = "+rez)
      println("\n\n\n")
      //      println(normalizeSClause(sClauseComposition(rez, X)))
      println("\n\n\n\n")
      ok
    }
  }
}

