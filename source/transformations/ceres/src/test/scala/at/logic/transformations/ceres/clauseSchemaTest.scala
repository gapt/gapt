package at.logic.transformations.ceres.clauseSchema

import at.logic.algorithms.shlk._
import at.logic.calculi.lk.base.{LKProof, FSequent}
import at.logic.calculi.lk._
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.language.schema._
import at.logic.language.lambda.types._
import java.io.File.separator
import org.junit.runner.RunWith
import org.specs2.execute.Success
import org.specs2.mutable._
import org.specs2.runner.JUnitRunner
import scala.io._

@RunWith(classOf[JUnitRunner])
class clauseSchemaTest extends SpecificationWithJUnit {
  "clauseSchemaTest" should {
    "create a correct schema clause" in {
      val k = IntVar("k")
      val n1 = Succ(k); val n2 = Succ(n1); val n3 = Succ(n2)
      val k1 = Succ(k); val k2 = Succ(n1); val k3 = Succ(n2)
      val zero = IntZero(); val one = Succ(IntZero()); val two = Succ(Succ(IntZero())); val three = Succ(Succ(Succ(IntZero())))
      val four = Succ(three);val five = Succ(four); val six = Succ(Succ(four));val seven = Succ(Succ(five));       
      val A0 = IndexedPredicate("A", IntZero())

      val Pk = IndexedPredicate("P", k)
      val P0 = IndexedPredicate("P", IntZero())
      val Q0 = IndexedPredicate("Q", IntZero())
      val Pk1 = IndexedPredicate("P", Succ(k))
      val c0 = nonVarSclause(List.empty[SchemaFormula], P0::Nil)
      val ck1 = nonVarSclause(List.empty[SchemaFormula], Pk1::Nil)
      val X = sClauseVar("X")
      val base: sClause = sClauseComposition(c0, X)
      val rec: sClause = sClauseComposition(ck1, X)
      val non = nonVarSclause(Q0::Nil, List.empty[SchemaFormula])
      val map = Map[sClauseVar, sClause]() + Tuple2(X.asInstanceOf[sClauseVar], non)
      val l = Ti::To::Tindex::Nil
      l.foldLeft(To.asInstanceOf[TA])((x,t) => ->(x, t))

      ok
    }


    "create a fist-order schema clause" in {
      val k = IntVar("k")
      val l = IntVar("l")
      val n1 = Succ(k); val n2 = Succ(n1); val n3 = Succ(n2)

      val zero = IntZero(); 
      val one = Succ(IntZero()); 
      val two = Succ(Succ(IntZero())); 
      val three = Succ(Succ(Succ(IntZero())))
      val four = Succ(three);
      val five = Succ(four); 
      val six = Succ(Succ(four));val seven = Succ(Succ(five));       
      val A0 = IndexedPredicate("A", IntZero())

      val Pk1 = IndexedPredicate("P", Succ(k))
      val X = sClauseVar("X")
      val x = fo2Var("x")
      val P = SchemaConst("P", ->(Ti, To))
      val g = SchemaConst("g", ->(Ti,Ti))
      val sigma0x0 = sTermN("σ", zero::x::zero::Nil)
      val sigmaskxsk = sTermN("σ", Succ(k)::x::Succ(k)::Nil)
      val Psigma0x0 = Atom(P, sigma0x0::Nil)
      val Psigmaskxsk = Atom(P, sigmaskxsk::Nil)

      // --- trs sigma ---
      val sigma_base = sTermN("σ", zero::x::l::Nil)
      val sigma_rec = sTermN("σ", Succ(k)::x::l::Nil)
      val st = sTermN("σ", k::x::l::Nil)
      val rewrite_base = indexedFOVar("x", l)
      val rewrite_step = SchemaApp(g, st)
      var trsSigma = dbTRSsTermN("σ", Tuple2(sigma_base, rewrite_base), Tuple2(sigma_rec, rewrite_step))

      // --- trs clause schema ---
      val c1 = clauseSchema("c", k::x::X::Nil)
      val ck = clauseSchema("c", Succ(k)::x::X::Nil)
      val c0 = clauseSchema("c", zero::x::X::Nil)
      val clauseSchBase: sClause = sClauseComposition(X, nonVarSclause(Nil, Psigma0x0::Nil))
      val clauseSchRec: sClause = sClauseComposition(c1, nonVarSclause(Nil, Psigmaskxsk::Nil))
      val trsClauseSch = dbTRSclauseSchema("c", Tuple2(c0, clauseSchBase), Tuple2(ck, clauseSchRec))
      // ----------

      val map = Map[SchemaVar, SchemaExpression]() + Tuple2(k, two) + Tuple2(l, three)
      val subst = Substitution(map)

      val sig = subst(trsSigma.map.get("σ").get._2._1)
      val sigma3 = unfoldSTermN(sig, trsSigma)

      val clause3 = applySubToSclauseOrSclauseTerm(subst, trsClauseSch.map.get("c").get._2._1).asInstanceOf[sClause]
      val rwclause3 = unfoldSchemaClause(clause3, trsClauseSch, trsSigma, subst)

      // --- trs sigma' ---
      val a = SchemaVar("a", Ti)
      val sigma1_base = sTermN("σ'", zero::Nil)
      val sigma1_rec = sTermN("σ'", Succ(k)::Nil)
      val st1 = sTermN("σ'", k::Nil)
      val rewrite_base1 = a
      val rewrite_step1 = SchemaApp(g, st1)
      trsSigma = trsSigma.add("σ'", Tuple2(sigma1_base, rewrite_base1), Tuple2(sigma1_rec, rewrite_step1))

      val sig1 = subst(trsSigma.map.get("σ'").get._1._1)
      val sigma13 = unfoldSTermN(sig, trsSigma)
      val sclterm = sclTimes(sclPlus(c1, ck), sclTermVar("ξ"))
      val groundsterm = applySubToSclauseOrSclauseTerm(subst, sclterm)
      val clauseSubst = new sClauseVarSubstitution(Map[sClauseVar, nonVarSclause]() + Tuple2(X.asInstanceOf[sClauseVar], nonVarSclause(Psigmaskxsk::Nil, Psigma0x0::Nil)))
      val cl = trsClauseSch.map.get("c").get._2._1
      
      ok
    }

    "create a schema clause term : ⊗ and ⊕ " in {
      val k = IntVar("k")
      val X = sClauseVar("X")
      val g = SchemaVar("g", ->(Ti,Ti))
      val x = fo2Var("x")
      val zero = IntZero(); 
      val one = Succ(IntZero()); 
      val two = Succ(Succ(IntZero())); 
      val three = Succ(Succ(Succ(IntZero())))
      val a = SchemaVar("a", Ti)
      val sigma1_base = sTermN("σ'", zero::Nil)
      val sigma1_rec = sTermN("σ'", Succ(k)::Nil)
      val st1 = sTermN("σ'", k::Nil)
      val rewrite_base1 = a
      val rewrite_step1 = SchemaApp(g, st1)
      val P = SchemaConst("P", ->(Ti, To))
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
      val pair1base = Tuple2(d1base, sclPlus(d2base, xi))
      val pair1step = Tuple2(d1step, sclPlus(d2step, cstep))
      val pair2base = Tuple2(d2base, nonVarSclause(Pa::Nil, Nil))
      val pair2step = Tuple2(d2step, sclPlus(d2k, nonVarSclause(Psig1::Nil, Nil)))
      val c1 = clauseSchema("c", k::x::X::Nil)
      val ck = clauseSchema("c", Succ(k)::x::X::Nil)
      val c0 = clauseSchema("c", zero::x::X::Nil)
      val sigma0x0 = sTermN("σ", zero::x::zero::Nil)
      val sigmaskxsk = sTermN("σ", Succ(k)::x::Succ(k)::Nil)
      val Psigma0x0 = Atom(P, sigma0x0::Nil)
      val Psigmaskxsk = Atom(P, sigmaskxsk::Nil)
      val clauseSchBase: sClause = sClauseComposition(X, nonVarSclause(Nil, Psigma0x0::Nil))
      val clauseSchRec: sClause = sClauseComposition(c1, nonVarSclause(Nil, Psigmaskxsk::Nil))
      val trsClauseSch = dbTRSclauseSchema("c", Tuple2(c0, clauseSchBase), Tuple2(ck, clauseSchRec))
      val trsSigma = dbTRSsTermN("σ'", Tuple2(sigma1_base, rewrite_base1), Tuple2(sigma1_rec, rewrite_step1))
      val trsSCLterm = dbTRSclauseSetTerm("d1", pair1base, pair1step)
      trsSCLterm.add("d2", pair2base, pair2step)

      val map = Map[SchemaVar, SchemaExpression]() + Tuple2(k, two)
      val subst = Substitution(map)
      val d1step_ground = applySubToSclauseOrSclauseTerm(subst, d1step)

      val mapX = Map[sClauseVar, sClause]() + Tuple2(X.asInstanceOf[sClauseVar], nonVarSclause(Nil, Nil))

      val rhoBase = ResolutionProofSchema("ρ", zero::x::X::Nil)
      val rhoStep = ResolutionProofSchema("ρ", Succ(k)::x::X::Nil)
      val rwBase = rTerm(sClauseComposition(nonVarSclause(Nil, Atom(P, sTermN("σ", zero::x::zero::Nil)::Nil)::Nil), X), nonVarSclause(Atom(P, sTermN("σ'", zero::Nil)::Nil)::Nil , Nil) , Atom(P, sTermN("σ", zero::x::zero::Nil)::Nil))
      val rwStep = rTerm(ResolutionProofSchema("ρ", k::x::sClauseComposition(nonVarSclause(Nil, Atom(P, sTermN("σ", Succ(k)::x::Succ(k)::Nil)::Nil)::Nil), X)::Nil),              nonVarSclause(Atom(P, sTermN("σ'", Succ(k)::Nil)::Nil)::Nil , Nil) , Atom(P, sTermN("σ", Succ(k)::x::Succ(k)::Nil)::Nil))
      resolutionProofSchemaDB.clear
      resolutionProofSchemaDB.add("ρ", Tuple2(rhoBase, rwBase), Tuple2(rhoStep, rwStep))
      ok
    }

    "check 1" in {
      val k = IntVar("k")
      val l = IntVar("l")
      val n1 = Succ(k); 
      val n2 = Succ(n1); 
      val n3 = Succ(n2)

      val zero = IntZero(); 
      val one = Succ(IntZero()); 
      val two = Succ(Succ(IntZero())); 
      val three = Succ(Succ(Succ(IntZero())))
      val four = Succ(three);
      val five = Succ(four); 
      val six = Succ(Succ(four));val seven = Succ(Succ(five));       
      val A0 = IndexedPredicate("A", IntZero())

      val Pk1 = IndexedPredicate("P", Succ(k))
      val X = sClauseVar("X")
      val x = fo2Var("x")
      val P = SchemaConst("P", ->(Ti, To))
      val g = SchemaConst("g", ->(Ti,Ti))
      val sigma0x0 = sTermN("σ", zero::x::zero::Nil)
      val sigmaskxsk = sTermN("σ", Succ(k)::x::Succ(k)::Nil)
      val Psigma0x0 = Atom(P, sigma0x0::Nil)
      val Psigmaskxsk = Atom(P, sigmaskxsk::Nil)

      // --- trs sigma ---
      val sigma_base = sTermN("σ", zero::x::l::Nil)
      val sigma_rec = sTermN("σ", Succ(k)::x::l::Nil)
      val st = sTermN("σ", k::x::l::Nil)
      val rewrite_base = indexedFOVar("x", l)
      val rewrite_step = SchemaApp(g, st)
      var trsSigma = dbTRSsTermN("σ", Tuple2(sigma_base, rewrite_base), Tuple2(sigma_rec, rewrite_step))

      // --- trs clause schema ---
      val c1 = clauseSchema("c", k::x::X::Nil)
      val ck = clauseSchema("c", Succ(k)::x::X::Nil)
      val c0 = clauseSchema("c", zero::x::X::Nil)
      val clauseSchBase: sClause = sClauseComposition(X, nonVarSclause(Nil, Psigma0x0::Nil))
      val clauseSchRec: sClause = sClauseComposition(c1, nonVarSclause(Nil, Psigmaskxsk::Nil))
      val trsClauseSch = dbTRSclauseSchema("c", Tuple2(c0, clauseSchBase), Tuple2(ck, clauseSchRec))
      // ----------

      val map = Map[SchemaVar, SchemaExpression]() + Tuple2(k, two) + Tuple2(l, three)
      val subst = Substitution(map)

      val sig = subst(trsSigma.map.get("σ").get._2._1)
      val sigma3 = unfoldSTermN(sig, trsSigma)

      val clause3 = applySubToSclauseOrSclauseTerm(subst, trsClauseSch.map.get("c").get._2._1).asInstanceOf[sClause]
      val rwclause3 = unfoldSchemaClause(clause3, trsClauseSch, trsSigma, subst)
      ok
    }

    "check 2" in {
      val l = IntVar("l")
      val k = IntVar("k")
      val X = sClauseVar("X")
      val g = SchemaConst("g", ->(Ti,Ti))
      val x = fo2Var("x")
      val zero = IntZero(); val one = Succ(IntZero()); val two = Succ(Succ(IntZero())); val three = Succ(Succ(Succ(IntZero())))
      val a = SchemaVar("a", Ti)
      val sigma1_base = sTermN("σ'", zero::Nil)
      val sigma1_rec = sTermN("σ'", Succ(k)::Nil)
      val st1 = sTermN("σ'", k::Nil)

      val rewrite_base1 = a
      val rewrite_step1 = SchemaApp(g, st1)
      val P = SchemaConst("P", ->(Ti, To))
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
      val pair1base = Tuple2(d1base, sclPlus(d2base, xi))
      val pair1step = Tuple2(d1step, sclPlus(d2step, cstep))
      val pair2base = Tuple2(d2base, nonVarSclause(Pa::Nil, Nil))
      val pair2step = Tuple2(d2step, sclPlus(d2k, nonVarSclause(Psig1::Nil, Nil)))
      val c1 = clauseSchema("c", k::x::X::Nil)
      val ck = clauseSchema("c", Succ(k)::x::X::Nil)
      val c0 = clauseSchema("c", zero::x::X::Nil)
      val sigma0x0 = sTermN("σ", zero::x::zero::Nil)
      val sigmaskxsk = sTermN("σ", Succ(k)::x::Succ(k)::Nil)
      val Psigma0x0 = Atom(P, sigma0x0::Nil)
      val Psigmaskxsk = Atom(P, sigmaskxsk::Nil)
      val clauseSchBase: sClause = sClauseComposition(X, nonVarSclause(Nil, Psigma0x0::Nil))
      val clauseSchRec: sClause = sClauseComposition(c1, nonVarSclause(Nil, Psigmaskxsk::Nil))
      val trsClauseSch = dbTRSclauseSchema("c", Tuple2(c0, clauseSchBase), Tuple2(ck, clauseSchRec))
      val trsSCLterm = dbTRSclauseSetTerm("d1", pair1base, pair1step)
      val sigma_base = sTermN("σ", zero::x::l::Nil)
      val sigma_rec = sTermN("σ", Succ(k)::x::l::Nil)
      val st = sTermN("σ", k::x::l::Nil)
      val rewrite_base = indexedFOVar("x", l)
      val rewrite_step = SchemaApp(g, st)
      var trsSigma = dbTRSsTermN("σ", Tuple2(sigma_base, rewrite_base), Tuple2(sigma_rec, rewrite_step))


      trsSCLterm.add("d2", pair2base, pair2step)

      val map = Map[SchemaVar, SchemaExpression]() + Tuple2(k, two) + Tuple2(l, three)
      val subst = Substitution(map)

      val clause3 = applySubToSclauseOrSclauseTerm(subst, trsClauseSch.map.get("c").get._2._1).asInstanceOf[sClause]
      val rwclause3 = unfoldSchemaClause(clause3, trsClauseSch, trsSigma, subst)

      ok
    }

    "check resolution deduction" in {
      skipped("Class cast exception")

      val l = IntVar("l")
      val k = IntVar("k")
      val X = sClauseVar("X")
      val g = SchemaConst("g", ->(Ti,Ti))
      val x = fo2Var("x")
      val zero = IntZero(); val one = Succ(IntZero()); val two = Succ(Succ(IntZero())); val three = Succ(Succ(Succ(IntZero())))
      val a = SchemaVar("a", Ti)
      val sigma1_base = sTermN("σ'", zero::Nil)
      val sigma1_rec = sTermN("σ'", Succ(k)::Nil)
      val st1 = sTermN("σ'", k::Nil)

      val rewrite_base1 = a 
      val rewrite_step1 = SchemaApp(g, st1)
      val P = SchemaConst("P", ->(Ti, To))
      val c = SchemaConst("c", Ti)
      val b = SchemaConst("b", Ti)
      val Pc = SchemaApp(P, c)
      val Pa = SchemaApp(P, a)
      val Pb = SchemaApp(P, b)

      val sigma_base = sTermN("σ", zero::x::l::Nil)
      val sigma_rec = sTermN("σ", Succ(k)::x::l::Nil)
      val st = sTermN("σ", k::x::l::Nil)
      val rewrite_base = SchemaApp(x, l)
      val rewrite_step = SchemaApp(g, st)
      var trsSigma = dbTRSsTermN("σ", Tuple2(sigma_base, rewrite_base), Tuple2(sigma_rec, rewrite_step))

      trsSigma = trsSigma.add("σ'", Tuple2(sigma1_base, rewrite_base1), Tuple2(sigma1_rec, rewrite_step1))
      val c1 = clauseSchema("c", k::x::X::Nil)
      val ck = clauseSchema("c", Succ(k)::x::X::Nil)
      val c0 = clauseSchema("c", zero::x::X::Nil)
      val sigma0x0 = sTermN("σ", zero::x::zero::Nil)
      val sigmaskxsk = sTermN("σ", Succ(k)::x::Succ(k)::Nil)
      val Psigma0x0 = Atom(P, sigma0x0::Nil)
      val Psigmaskxsk = Atom(P, sigmaskxsk::Nil)
      val clauseSchBase: sClause = sClauseComposition(X, nonVarSclause(Nil, Psigma0x0::Nil))
      val clauseSchRec: sClause = sClauseComposition(c1, nonVarSclause(Nil, Psigmaskxsk::Nil))
      val trsClauseSch = dbTRSclauseSchema("c", Tuple2(c0, clauseSchBase), Tuple2(ck, clauseSchRec))

      val map = Map[SchemaVar, SchemaExpression]() + Tuple2(k, two) + Tuple2(l, three)
      val subst = Substitution(map)

      val sig1 = subst(trsSigma.map.get("σ'").get._2._1)
      val sigma13 = unfoldSTermN(sig1, trsSigma)
      val f = SchemaApp(P, sig1)
      val Psig1 = unfoldGroundAtom(f.asInstanceOf[SchemaFormula], trsSigma)

      val mapX = Map[sClauseVar, sClause]() + Tuple2(X.asInstanceOf[sClauseVar], nonVarSclause(Nil, Nil))

      val clause3 = applySubToSclauseOrSclauseTerm(subst, trsClauseSch.map.get("c").get._2._1).asInstanceOf[sClause]
      val de = deComposeSClause(unfoldSchemaClause(clause3, trsClauseSch, trsSigma, subst))

      val rhoBase = ResolutionProofSchema("ρ", zero::x::X::Nil)
      val rhoStep = ResolutionProofSchema("ρ", Succ(k)::x::X::Nil)
      val rwBase = rTerm(sClauseComposition(nonVarSclause(Nil, Atom(P, sTermN("σ", zero::x::zero::Nil)::Nil)::Nil), X), nonVarSclause(Atom(P, sTermN("σ'", zero::Nil)::Nil)::Nil , Nil) , Atom(P, sTermN("σ", zero::x::zero::Nil)::Nil))
      val rwStep = rTerm(ResolutionProofSchema("ρ", k::x::sClauseComposition(nonVarSclause(Nil, Atom(P, sTermN("σ", Succ(k)::x::Succ(k)::Nil)::Nil)::Nil), X)::Nil),              nonVarSclause(Atom(P, sTermN("σ'", Succ(k)::Nil)::Nil)::Nil , Nil) , Atom(P, sTermN("σ", Succ(k)::x::Succ(k)::Nil)::Nil))
      resolutionProofSchemaDB.clear
      resolutionProofSchemaDB.add("ρ", Tuple2(rhoBase, rwBase), Tuple2(rhoStep, rwStep))
      val base = resolutionProofSchemaDB.map.get("ρ").get._1._2
      var step = ResolutionProofSchema("ρ", three::x::X::Nil)
      step = sClauseVarSubstitution(step, mapX).asInstanceOf[ResolutionProofSchema]

      val rez2 = unfoldingAtomsInResTerm(step, trsSigma, subst)
      val h = SchemaAbs(k, a)
      val mapfo2 = Map[fo2Var, SchemaExpression]() + Tuple2(x.asInstanceOf[fo2Var], h)
      val rez3 = unfoldResolutionProofSchema(rez2)
      val fo2sub = fo2VarSubstitution(rez3, mapfo2).asInstanceOf[sResolutionTerm]

      val rez4 = resolutionDeduction(fo2sub, trsClauseSch, trsSigma, subst, mapX)
      
      ok
    }
  }
}

