package at.logic.transformations.ceres.clauseSchema

import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.algorithms.shlk._
import java.io.File.separator
import scala.io._
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import org.specs2.execute.Success
import at.logic.language.lambda.types._
import at.logic.language.hol._
import at.logic.language.lambda.typedLambdaCalculus.{LambdaExpression, Var}
import at.logic.calculi.lk.base.{LKProof, FSequent}
import at.logic.calculi.lk.propositionalRules.ContractionLeftRule._
import at.logic.calculi.lk.propositionalRules.{ContractionLeftRule, Axiom, NegLeftRule}

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
      val rez = clause_schema(two, map)
      println("\nclause_schema = "+rez)
      println("\n\n\n")
//      println(deComposeSClause(sClauseComposition(rez, X)))
//      println(Pred(two))
      println("\n\n\n\n")
      ok
    }


    "create a fist-order schema clause" in {
      println(Console.RED+"\n\n       clauseSchemaTest and trsTest\n\n"+Console.RESET)
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
      println("\n\n\nunfolding : \n\n"+rwclause3)
      println("\n\n\noptimizing : \n\n"+deComposeSClause(rwclause3))

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
      val clauseSubst = new sClauseVarSubstitution(Map[sClauseVar, nonVarSclause]() + Pair(X.asInstanceOf[sClauseVar], nonVarSclause(Psigmaskxsk::Nil, Psigma0x0::Nil)))
      val cl = trsClauseSch.map.get("c").get._2._1
      println("\n\n"+clauseSubst(applySubToSclauseOrSclauseTerm(subst, cl).asInstanceOf[sClause]))
      //----------------------

      println("\n\n")
      ok
    }

    "create a schema clause term : ⊗ and ⊕ " in {
      println(Console.RED+"\n\n       clauseSchemaTermTest\n\n"+Console.RESET)
      val k = IntVar(new VariableStringSymbol("k"))
      val X = sClauseVar("X")
      val g = HOLVar(new VariableStringSymbol("g"), ->(Ti(),Ti()))
      val x = fo2Var(new VariableStringSymbol("x"))
      val zero = IntZero(); val one = Succ(IntZero()); val two = Succ(Succ(IntZero())); val three = Succ(Succ(Succ(IntZero())))
      val a = HOLVar(new VariableStringSymbol("a"), Ti())
      val sigma1_base = sTermN("σ'", zero::Nil)
      val sigma1_rec = sTermN("σ'", Succ(k)::Nil)
      val st1 = sTermN("σ'", k::Nil)
      val rewrite_base1 = a
      val rewrite_step1 = HOLApp(g, st1)
      val P = HOLConst(new ConstantStringSymbol("P"), ->(Ti(), To()))
      val d1base = clauseSetTerm("d1", zero::x::X::Nil)
      val d1step = clauseSetTerm("d1", Succ(k)::x::X::Nil)
      val d2base = clauseSetTerm("d2", zero::x::X::Nil)
      val d2step = clauseSetTerm("d2", Succ(k)::x::X::Nil)
      val d2k = clauseSetTerm("d2", k::x::X::Nil)
      val cstep = clauseSchema("c", Succ(k)::x::X::Nil)
      val cbase = clauseSchema("c", zero::x::X::Nil)
      val Pa = Atom(P, a::Nil)
      val Psig1 = Atom(P, sigma1_rec::Nil)
      val xi = sclTermVar("ξ")
      val pair1base = Pair(d1base, sclPlus(d2base, xi))
      val pair1step = Pair(d1step, sclPlus(d2step, cstep))
      val pair2base = Pair(d2base, nonVarSclause(Pa::Nil, Nil))
      val pair2step = Pair(d2step, sclPlus(d2k, nonVarSclause(Psig1::Nil, Nil)))
      val c1 = clauseSchema("c", k::x::X::Nil)
      val ck = clauseSchema("c", Succ(k)::x::X::Nil)
      val c0 = clauseSchema("c", zero::x::X::Nil)
      val sigma0x0 = sTermN("σ", zero::x::zero::Nil)
      val sigmaskxsk = sTermN("σ", Succ(k)::x::Succ(k)::Nil)
      val Psigma0x0 = Atom(P, sigma0x0::Nil)
      val Psigmaskxsk = Atom(P, sigmaskxsk::Nil)
      val clauseSchBase: sClause = sClauseComposition(X, nonVarSclause(Nil, Psigma0x0::Nil))
      val clauseSchRec: sClause = sClauseComposition(c1, nonVarSclause(Nil, Psigmaskxsk::Nil))
      val trsClauseSch = dbTRSclauseSchema("c", Pair(c0, clauseSchBase), Pair(ck, clauseSchRec))
      val trsSigma = dbTRSsTermN("σ'", Pair(sigma1_base, rewrite_base1), Pair(sigma1_rec, rewrite_step1))
      val trsSCLterm = dbTRSclauseSetTerm("d1", pair1base, pair1step)
      trsSCLterm.add("d2", pair2base, pair2step)

      val map = Map[Var, HOLExpression]() + Pair(k.asInstanceOf[Var], two)
      val subst = new SchemaSubstitution3(map)
      println("\nd1step = "+d1step)
      val d1step_ground = applySubToSclauseOrSclauseTerm(subst, d1step)
      println(d1step_ground)

      val unfold_d1step_ground = unfoldClauseSetTerm(d1step_ground, trsSCLterm, trsClauseSch, trsSigma, subst, false, false)
      println(unfold_d1step_ground)
      val mapX = Map[sClauseVar, sClause]() + Pair(X.asInstanceOf[sClauseVar], nonVarSclause(Nil, Nil))

      val rwd1step_ground = RewriteClauseSchemaInSclauseTerm(unfold_d1step_ground, trsClauseSch, trsSigma, subst, mapX)
      println("rwd1step_ground = "+rwd1step_ground)

      val rwd1step_ground_toSet = clauseSetTermToSet(rwd1step_ground)
      println("\n\nclause set : \n\n{\n"+rwd1step_ground_toSet.head);rwd1step_ground_toSet.tail.foreach(x => println(" ; "+unfoldSchemaClause(x,trsClauseSch, trsSigma, subst)));println("}")
//      println(trsSigma.map)
//      println(trsClauseSch.map)
      println("\n\n")

      println(trsSCLterm.map)

      println("\n\n")
      val rhoBase = ResolutionProofSchema("ρ", zero::x::X::Nil)
      val rhoStep = ResolutionProofSchema("ρ", Succ(k)::x::X::Nil)
      val rwBase = rTerm(sClauseComposition(nonVarSclause(Nil, Atom(P, sTermN("σ", zero::x::zero::Nil)::Nil)::Nil), X), nonVarSclause(Atom(P, sTermN("σ'", zero::Nil)::Nil)::Nil , Nil) , Atom(P, sTermN("σ", zero::x::zero::Nil)::Nil))
      val rwStep = rTerm(ResolutionProofSchema("ρ", k::x::sClauseComposition(nonVarSclause(Nil, Atom(P, sTermN("σ", Succ(k)::x::Succ(k)::Nil)::Nil)::Nil), X)::Nil),              nonVarSclause(Atom(P, sTermN("σ'", Succ(k)::Nil)::Nil)::Nil , Nil) , Atom(P, sTermN("σ", Succ(k)::x::Succ(k)::Nil)::Nil))
//      val trsRes = dbTRSresolutionSchema("ρ", Pair(rhoBase, rwBase), Pair(rhoStep, rwStep))
      dbTRSresolutionSchema.clear
      dbTRSresolutionSchema.add("ρ", Pair(rhoBase, rwBase), Pair(rhoStep, rwStep))
      println("\ntrsRes = "+dbTRSresolutionSchema.map )
      println("\n\n")
      ok
    }

    "check 1" in {
      println(Console.RED+"\n\n       check1\n\n"+Console.RESET)
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

      val clause3 = applySubToSclauseOrSclauseTerm(subst, trsClauseSch.map.get("c").get._2._1).asInstanceOf[sClause]
      println("\n\nclause schema for instance "+Console.RED+printSchemaProof.formulaToString(map.get(k).get)+Console.RESET+" :\n" )
      println(clause3)
      val rwclause3 = unfoldSchemaClause(clause3, trsClauseSch, trsSigma, subst)
      println("\n\n\nunfolding : \n\n"+rwclause3)
      println("\n\n\noptimizing : \n\n"+deComposeSClause(rwclause3))

      println("\n\n")
      ok
    }

    "check 2" in {
      println(Console.RED+"\n\n       check 2\n\n"+Console.RESET)
      val l = IntVar(new VariableStringSymbol("l"))
      val k = IntVar(new VariableStringSymbol("k"))
      val X = sClauseVar("X")
      val g = HOLVar(new VariableStringSymbol("g"), ->(Ti(),Ti()))
      val x = fo2Var(new VariableStringSymbol("x"))
      val zero = IntZero(); val one = Succ(IntZero()); val two = Succ(Succ(IntZero())); val three = Succ(Succ(Succ(IntZero())))
      val a = HOLVar(new VariableStringSymbol("a"), Ti())
      val sigma1_base = sTermN("σ'", zero::Nil)
      val sigma1_rec = sTermN("σ'", Succ(k)::Nil)
      val st1 = sTermN("σ'", k::Nil)

      val rewrite_base1 = a
      val rewrite_step1 = HOLApp(g, st1)
      val P = HOLConst(new ConstantStringSymbol("P"), ->(Ti(), To()))
      val d1base = clauseSetTerm("d1", zero::x::X::Nil)
      val d1step = clauseSetTerm("d1", Succ(k)::x::X::Nil)
      val d2base = clauseSetTerm("d2", zero::x::X::Nil)
      val d2step = clauseSetTerm("d2", Succ(k)::x::X::Nil)
      val d2k = clauseSetTerm("d2", k::x::X::Nil)
      val cstep = clauseSchema("c", Succ(k)::x::X::Nil)
      val cbase = clauseSchema("c", zero::x::X::Nil)
      val Pa = Atom(P, a::Nil)
      val Psig1 = Atom(P, sigma1_rec::Nil)
      val xi = sclTermVar("ξ")
      val pair1base = Pair(d1base, sclPlus(d2base, xi))
      val pair1step = Pair(d1step, sclPlus(d2step, cstep))
      val pair2base = Pair(d2base, nonVarSclause(Pa::Nil, Nil))
      val pair2step = Pair(d2step, sclPlus(d2k, nonVarSclause(Psig1::Nil, Nil)))
      val c1 = clauseSchema("c", k::x::X::Nil)
      val ck = clauseSchema("c", Succ(k)::x::X::Nil)
      val c0 = clauseSchema("c", zero::x::X::Nil)
      val sigma0x0 = sTermN("σ", zero::x::zero::Nil)
      val sigmaskxsk = sTermN("σ", Succ(k)::x::Succ(k)::Nil)
      val Psigma0x0 = Atom(P, sigma0x0::Nil)
      val Psigmaskxsk = Atom(P, sigmaskxsk::Nil)
      val clauseSchBase: sClause = sClauseComposition(X, nonVarSclause(Nil, Psigma0x0::Nil))
      val clauseSchRec: sClause = sClauseComposition(c1, nonVarSclause(Nil, Psigmaskxsk::Nil))
      val trsClauseSch = dbTRSclauseSchema("c", Pair(c0, clauseSchBase), Pair(ck, clauseSchRec))
//      val trsSigma = dbTRSsTermN("σ'", Pair(sigma1_base, rewrite_base1), Pair(sigma1_rec, rewrite_step1))
      val trsSCLterm = dbTRSclauseSetTerm("d1", pair1base, pair1step)
      val sigma_base = sTermN("σ", zero::x::l::Nil)
      val sigma_rec = sTermN("σ", Succ(k)::x::l::Nil)
      val st = sTermN("σ", k::x::l::Nil)
      val rewrite_base = indexedFOVar(new VariableStringSymbol("x"), l)
      val rewrite_step = HOLApp(g, st)
      var trsSigma = dbTRSsTermN("σ", Pair(sigma_base, rewrite_base), Pair(sigma_rec, rewrite_step))


      trsSCLterm.add("d2", pair2base, pair2step)

      val map = Map[Var, HOLExpression]() + Pair(k.asInstanceOf[Var], two) + Pair(l.asInstanceOf[Var], three)
      val subst = new SchemaSubstitution3(map)

      val clause3 = applySubToSclauseOrSclauseTerm(subst, trsClauseSch.map.get("c").get._2._1).asInstanceOf[sClause]
      println("\n\nclause schema for instance "+Console.RED+printSchemaProof.formulaToString(map.get(k).get)+Console.RESET+" :\n" )
      println(clause3)
      val rwclause3 = unfoldSchemaClause(clause3, trsClauseSch, trsSigma, subst)
      println("\n\n\nunfolding : \n\n"+rwclause3)
      println("\n\n\noptimizing : \n\n"+deComposeSClause(rwclause3))

//
//      val map = Map[Var, HOLExpression]() + Pair(k.asInstanceOf[Var], two)
//      val subst = new SchemaSubstitution3(map)
//      println("\nd1step = "+d1step)
//      val d1step_ground = applySubToSclauseOrSclauseTerm(subst, d1step)
//      println(d1step_ground)
//
//      val unfold_d1step_ground = unfoldSchemaClauseTerm(d1step_ground, trsSCLterm, trsClauseSch, trsSigma, subst, false, false)
//      println(unfold_d1step_ground)
//      val mapX = Map[sClauseVar, sClause]() + Pair(X.asInstanceOf[sClauseVar], nonVarSclause(Nil, Nil))
//
//      val rwd1step_ground = RewriteClauseSetSchemaInClauseSchemaTerm(unfold_d1step_ground, trsClauseSch, trsSigma, subst, mapX)
//      println("rwd1step_ground = "+rwd1step_ground)
//
//      val rwd1step_ground_toSet = clauseSetTermToSet(rwd1step_ground)
//      println("\n\nclause set : \n\n{\n"+rwd1step_ground_toSet.head);rwd1step_ground_toSet.tail.foreach(x => println(" ; "+unfoldSchemaClause(x,trsClauseSch, trsSigma, subst)));println("}")

      println("\n\n")
      ok
    }

    "check resolution deduction" in {
      println(Console.RED+"\n\n       check resolution deduction\n\n"+Console.RESET)
      val l = IntVar(new VariableStringSymbol("l"))
      val k = IntVar(new VariableStringSymbol("k"))
      val X = sClauseVar("X")
      val g = HOLVar(new VariableStringSymbol("g"), ->(Ti(),Ti()))
      val x = fo2Var(new VariableStringSymbol("x"))
      val zero = IntZero(); val one = Succ(IntZero()); val two = Succ(Succ(IntZero())); val three = Succ(Succ(Succ(IntZero())))
      val a = HOLVar(new VariableStringSymbol("a"), Ti())
      val sigma1_base = sTermN("σ'", zero::Nil)
      val sigma1_rec = sTermN("σ'", Succ(k)::Nil)
      val st1 = sTermN("σ'", k::Nil)

      val rewrite_base1 = a //indexedFOVar(new VariableStringSymbol("x"), k)
      val rewrite_step1 = HOLApp(g, st1)
      val P = HOLConst(new ConstantStringSymbol("P"), ->(Ti(), To()))
      val c = HOLConst(new ConstantStringSymbol("c"), Ti())
      val b = HOLConst(new ConstantStringSymbol("b"), Ti())
      val Pc = HOLApp(P, c).asInstanceOf[HOLFormula]
      val Pa = HOLApp(P, a).asInstanceOf[HOLFormula]
      val Pb = HOLApp(P, b).asInstanceOf[HOLFormula]
//      val Px0 = HOLApp(P, indexedFOVar(new VariableStringSymbol("x"), zero)).asInstanceOf[HOLFormula]
//      val Px0copy = HOLApp(P, indexedFOVar(new VariableStringSymbol("x"), zero)).asInstanceOf[HOLFormula]
//      val Pgx1 = HOLApp(P, HOLApp(g, indexedFOVar(new VariableStringSymbol("x"), one))).asInstanceOf[HOLFormula]
//      val Px0 = HOLApp(P, HOLApp(x, zero)).asInstanceOf[HOLFormula]
//      val Px0copy = HOLApp(P, HOLApp(x, zero)).asInstanceOf[HOLFormula]
//      val Pgx1 = HOLApp(P, HOLApp(g, HOLApp(x, one))).asInstanceOf[HOLFormula]
//      val r1 = nonVarSclause(Px0::Pgx1::Nil, Pb::Nil)
//      val r2 = nonVarSclause(Pb::Nil, Pc::Nil)
      val sigma_base = sTermN("σ", zero::x::l::Nil)
      val sigma_rec = sTermN("σ", Succ(k)::x::l::Nil)
      val st = sTermN("σ", k::x::l::Nil)
//      val rewrite_base = indexedFOVar(new VariableStringSymbol("x"), l)
      val rewrite_base = HOLApp(x, l)
      val rewrite_step = HOLApp(g, st)
      var trsSigma = dbTRSsTermN("σ", Pair(sigma_base, rewrite_base), Pair(sigma_rec, rewrite_step))

      trsSigma = trsSigma.add("σ'", Pair(sigma1_base, rewrite_base1), Pair(sigma1_rec, rewrite_step1))
      val c1 = clauseSchema("c", k::x::X::Nil)
      val ck = clauseSchema("c", Succ(k)::x::X::Nil)
      val c0 = clauseSchema("c", zero::x::X::Nil)
      val sigma0x0 = sTermN("σ", zero::x::zero::Nil)
      val sigmaskxsk = sTermN("σ", Succ(k)::x::Succ(k)::Nil)
      val Psigma0x0 = Atom(P, sigma0x0::Nil)
      val Psigmaskxsk = Atom(P, sigmaskxsk::Nil)
      val clauseSchBase: sClause = sClauseComposition(X, nonVarSclause(Nil, Psigma0x0::Nil))
      val clauseSchRec: sClause = sClauseComposition(c1, nonVarSclause(Nil, Psigmaskxsk::Nil))
      val trsClauseSch = dbTRSclauseSchema("c", Pair(c0, clauseSchBase), Pair(ck, clauseSchRec))


      println("\n\n")
      val map = Map[Var, HOLExpression]() + Pair(k.asInstanceOf[Var], two) + Pair(l.asInstanceOf[Var], three)
      val subst = new SchemaSubstitution3(map)

      val sig1 = subst(trsSigma.map.get("σ'").get._2._1)
      println("\n\nsig1 = "+sig1)
      val sigma13 = unfoldSTermN(sig1, trsSigma)
      println("\n\nsigma13 = "+sigma13)
      val f = HOLApp(P, sig1).asInstanceOf[HOLFormula]
      val Psig1 = unfoldGroundAtom(f, trsSigma, subst)
      println("\n\nPsig1 = "+Psig1)
      println("\n\n")

      val mapX = Map[sClauseVar, sClause]() + Pair(X.asInstanceOf[sClauseVar], nonVarSclause(Nil, Nil))
      
//      val mapFO2Var = Map[HOLVar, HOLExpression]() + Pair(x, HOLAbs(y, ))
      val clause3 = applySubToSclauseOrSclauseTerm(subst, trsClauseSch.map.get("c").get._2._1).asInstanceOf[sClause]
      val de = deComposeSClause(unfoldSchemaClause(clause3, trsClauseSch, trsSigma, subst))
      println("deComposeSClause = "+de)
      println("deComposeSClause2 = "+deComposeSClause(de))


//      val r = rTerm(sClauseComposition(nonVarSclause(Psig1::Nil, Pc::Nil), nonVarSclause(Nil, Pb::Nil))  , rTerm(rTerm(r1, r2, Pb), nonVarSclause(Pc::Nil, Nil), Pc), Pc)
//      val r = rTerm( clause3 , rTerm(rTerm(r1, r2, Pb), nonVarSclause(Pc::Nil, Nil), Pc), Px0copy)
//      println("\n\nr = "+r)
//      println("\n\n")
//      println("resDeduction(r) = "+resolutionDeduction(r, trsClauseSch, trsSigma, subst, mapX))
//      println("\n\n")

      val rhoBase = ResolutionProofSchema("ρ", zero::x::X::Nil)
      val rhoStep = ResolutionProofSchema("ρ", Succ(k)::x::X::Nil)
      val rwBase = rTerm(sClauseComposition(nonVarSclause(Nil, Atom(P, sTermN("σ", zero::x::zero::Nil)::Nil)::Nil), X), nonVarSclause(Atom(P, sTermN("σ'", zero::Nil)::Nil)::Nil , Nil) , Atom(P, sTermN("σ", zero::x::zero::Nil)::Nil))
      val rwStep = rTerm(ResolutionProofSchema("ρ", k::x::sClauseComposition(nonVarSclause(Nil, Atom(P, sTermN("σ", Succ(k)::x::Succ(k)::Nil)::Nil)::Nil), X)::Nil),              nonVarSclause(Atom(P, sTermN("σ'", Succ(k)::Nil)::Nil)::Nil , Nil) , Atom(P, sTermN("σ", Succ(k)::x::Succ(k)::Nil)::Nil))
//      val trsRes = dbTRSresolutionSchema("ρ", Pair(rhoBase, rwBase), Pair(rhoStep, rwStep))
      dbTRSresolutionSchema.clear
      dbTRSresolutionSchema.add("ρ", Pair(rhoBase, rwBase), Pair(rhoStep, rwStep))
      println(Console.BOLD+"\nresolution-rewriting system:\n\n"+Console.RESET+dbTRSresolutionSchema.map )
      val base = dbTRSresolutionSchema.map.get("ρ").get._1._2
//      val step = trsRes.map.get("ρ").get._2._1
      var step = ResolutionProofSchema("ρ", three::x::X::Nil)
      step = sClauseVarSubstitution(step, mapX).asInstanceOf[ResolutionProofSchema]
//      println("base = "+base)
      println(Console.BOLD+"\n\nunfolding the ground resolution term: \n\n"+Console.RESET+step)
//      val rez1 = sClauseVarSubstitution(base, mapX)
//      val rez1 = sClauseVarSubstitution(step, mapX)
//      println("\nrez1 = "+rez1)
      val rez2 = unfoldingAtomsInResTerm(step, trsSigma, subst)
//      println("\nrez2 = "+rez2)

      println(Console.BOLD+"\nterm-rewriting system: \n\n"+Console.RESET+trsSigma)

//      val h = HOLAbs(k, sTermN("σ'", k::Nil))
      val h = HOLAbs(k, a)
      println("\nh.type = "+h.exptype)
      val mapfo2 = Map[fo2Var, LambdaExpression]() + Pair(x.asInstanceOf[fo2Var], h)

      println(Console.BOLD+"substitutions:\n"+Console.RESET)
      println("1) arithmetical variables  : "+map)
      println("2) schema-clause variables : "+mapX)
      println("3) second-order variables  : "+mapfo2)



      val rez3 = unfoldResolutionProofSchema(rez2, trsClauseSch, trsSigma, subst, mapX)
      println(Console.BOLD+"\n\ngenerating resolution term: \n\n"+Console.RESET+rez3)

      val fo2sub = fo2VarSubstitution(rez3, mapfo2).asInstanceOf[sResolutionTerm]
      println(Console.BOLD+"\n\napplying second-order substitution:\n\n"+Console.RESET+fo2sub)

      val rez4 = resolutionDeduction(fo2sub, trsClauseSch, trsSigma, subst, mapX)
      println(Console.BOLD+"\n\nDeduction: \n\n"+Console.RESET+rez4)
      println("\n\n\n\n\n")



      println("\n\n\nc* = ")
      printSchemaProof(ResDeductionToLKTree(fo2sub))
      println("\n\n\n")
//     println("Xsubst = "+sClauseVarSubstitution(sClauseComposition(nonVarSclause(Nil, Atom(P, sTermN("σ", Succ(k)::x::Succ(k)::Nil)::Nil)::Nil), X), mapX))
//      resolutionDeduction(r) must beEqualTo (nonVarSclause(Pa::Nil, Pb::Nil))
                      ok
    }
  }
}

