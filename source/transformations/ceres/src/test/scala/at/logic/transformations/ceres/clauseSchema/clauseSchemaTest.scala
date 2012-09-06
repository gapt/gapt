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
      val clause_schema = ClauseSchemaPair(base, rec)
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
      val l = IntVar(new VariableStringSymbol("l"))
      val n1 = Succ(k); val n2 = Succ(n1); val n3 = Succ(n2)

      val zero = IntZero(); val one = Succ(IntZero()); val two = Succ(Succ(IntZero())); val three = Succ(Succ(Succ(IntZero())))
      val four = Succ(three);val five = Succ(four); val six = Succ(Succ(four));val seven = Succ(Succ(five));       val A0 = IndexedPredicate(new ConstantStringSymbol("A"), IntZero())

      val Pk1 = IndexedPredicate(new ConstantStringSymbol("P"), Succ(k))
      val X = sClauseVar("X")
      val x = fo2Var(new VariableStringSymbol("x"))
      val P = HOLConst(new ConstantStringSymbol("P"), ->(Ti(), To()))
      val g = HOLVar(new VariableStringSymbol("g"), ->(Ti(),Ti()))
      val sigma0x0 = sTermN("σ", zero::x::zero::Nil)
      val sigmaskxsk = sTermN("σ", Succ(k)::x::Succ(k)::Nil)
      val Psigma0x0 = Atom(P, sigma0x0::Nil)
      val Psigmaskxsk = Atom(P, sigmaskxsk::Nil)

      // --- trs sigma ---
      val sigma_base = sTermN("σ", zero::x::l::Nil)
      val sigma_rec = sTermN("σ", Succ(k)::x::l::Nil)
      val st = sTermN("σ", k::x::l::Nil)
      val rewrite_base = indexedFOVar(new VariableStringSymbol("x"), l)
      val rewrite_step = HOLApp(g, st)
      var trsSigma = dbTRSsTermN("σ", Pair(sigma_base, rewrite_base), Pair(sigma_rec, rewrite_step))

      // --- trs clause schema ---
      val c1 = clauseSchema("c", k::x::X::Nil)
      val ck = clauseSchema("c", Succ(k)::x::X::Nil)
      val c0 = clauseSchema("c", zero::x::X::Nil)
      val clauseSchBase: sClause = sClauseComposition(X, nonVarSclause(Nil, Psigma0x0::Nil))
      val clauseSchRec: sClause = sClauseComposition(c1, nonVarSclause(Nil, Psigmaskxsk::Nil))
      val trsClauseSch = dbTRSclauseSchema("c", Pair(c0, clauseSchBase), Pair(ck, clauseSchRec))
      // ----------

      val map = Map[Var, HOLExpression]() + Pair(k.asInstanceOf[Var], two) + Pair(l.asInstanceOf[Var], three)
      val subst = new SchemaSubstitution3(map)

      val sig = subst(trsSigma.map.get("σ").get._2._1)
//      println("sig = "+sig)
      val sigma3 = unfoldSTermN(sig, trsSigma)
//      println("\n\nsigma3 = "+sigma3)

      println(Console.RED+"\nrewriting systems :\n"+Console.RESET)

      println(trsSigma.map.get("σ").get._1._1 +Console.GREEN+"       →  "+Console.RESET+trsSigma.map.get("σ").get._1._2)
      println(trsSigma.map.get("σ").get._2._1 +Console.GREEN+"  →  "+Console.RESET+trsSigma.map.get("σ").get._2._2)

      println("\n\n"+trsClauseSch.map.get("c").get._1._1 +Console.GREEN+"    →  "+Console.RESET+trsClauseSch.map.get("c").get._1._2)
      println(trsClauseSch.map.get("c").get._2._1 +Console.GREEN+"  →  "+Console.RESET+trsClauseSch.map.get("c").get._2._2)


      val clause3 = applySubToSclauseOrSclauseTerm(subst, trsClauseSch.map.get("c").get._2._1).asInstanceOf[sClause]
      println("\n\nclause schema for instance "+Console.RED+printSchemaProof.formulaToString(map.get(k).get)+Console.RESET+" :\n" )
      println(clause3)
      val rwclause3 = unfoldSchemaClause(clause3, trsClauseSch, trsSigma, subst)
      println("\n\n\nnormalizing : \n\n"+rwclause3)
      println("\n\n\noptimizing : \n\n"+normalizeSClause(rwclause3))

      // --- trs sigma' ---
      val a = HOLVar(new VariableStringSymbol("a"), Ti())
      val sigma1_base = sTermN("σ'", zero::Nil)
      val sigma1_rec = sTermN("σ'", Succ(k)::Nil)
      val st1 = sTermN("σ'", k::Nil)
      val rewrite_base1 = a
      val rewrite_step1 = HOLApp(g, st1)
      trsSigma = trsSigma.add("σ'", Pair(sigma1_base, rewrite_base1), Pair(sigma1_rec, rewrite_step1))
      println("\n\n")

      println(trsSigma.map.get("σ'").get._1._1 +Console.GREEN+"       →  "+Console.RESET+trsSigma.map.get("σ'").get._1._2)
      println(trsSigma.map.get("σ'").get._2._1 +Console.GREEN+"  →  "+Console.RESET+trsSigma.map.get("σ'").get._2._2)
      val sig1 = subst(trsSigma.map.get("σ'").get._1._1)
      println("\n\n"+sig1)
      val sigma13 = unfoldSTermN(sig, trsSigma)
      println("\n\n"+printSchemaProof.formulaToString(sigma13))
      val sclterm = sclTimes(sclPlus(c1, ck), sclTermVar("ξ"))
      val groundsterm = applySubToSclauseOrSclauseTerm(subst, sclterm)
      println("\n\n"+unfoldSclauseTerm(groundsterm, trsClauseSch, trsSigma, subst))

      //----------------------

      println("\n\n")
      ok
    }
  }
}

