package at.logic.simple_schema_test

import at.logic.language.schema._
import at.logic.calculi.lk.base.Sequent
import at.logic.calculi.lk.propositionalRules.{OrLeftRule, NegLeftRule, Axiom}
import at.logic.calculi.lksk.Axiom
import at.logic.parsing.readers.StringReader
import org.specs2.mutable._
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import at.logic.language.hol._
import at.logic.language.hol.Definitions._
import at.logic.language.hol.ImplicitConverters._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.types.Definitions._
import at.logic.language.lambda.types._
import at.logic.language.lambda.symbols.ImplicitConverters._
import at.logic.parsing.readers.StringReader
import scala.io._
import java.io.File.separator
import java.io.{FileInputStream, InputStreamReader}
import org.specs2.execute.Success
import at.logic.gui.prooftool.gui.Main
import at.logic.algorithms.shlk._
import at.logic.transformations.ceres.clauseSchema.sClauseVar._
import at.logic.transformations.ceres.clauseSchema.fo2Var._
import at.logic.transformations.ceres.clauseSchema.sTermN._
import at.logic.transformations.ceres.clauseSchema.dbTRSsTermN._
import at.logic.transformations.ceres.clauseSchema.clauseSchema._
import at.logic.transformations.ceres.clauseSchema.sClauseComposition._
import at.logic.transformations.ceres.clauseSchema.nonVarSclause._
import at.logic.transformations.ceres.clauseSchema.dbTRSclauseSchema._
import at.logic.transformations.ceres.clauseSchema.unfoldSTermN._
import at.logic.transformations.ceres.clauseSchema.unfoldGroundAtom._
import at.logic.transformations.ceres.clauseSchema.applySubToSclauseOrSclauseTerm._
import at.logic.transformations.ceres.clauseSchema.deComposeSClause._
import at.logic.transformations.ceres.clauseSchema.unfoldSchemaClause._
import at.logic.transformations.ceres.clauseSchema.ResolutionProofSchema._
import at.logic.transformations.ceres.clauseSchema.rTerm._
import at.logic.transformations.ceres.clauseSchema.resolutionProofSchemaDB._
import at.logic.transformations.ceres.clauseSchema.sClauseVarSubstitution._
import at.logic.transformations.ceres.clauseSchema.unfoldingAtomsInResTerm._
import at.logic.transformations.ceres.clauseSchema.unfoldResolutionProofSchema._
import at.logic.transformations.ceres.clauseSchema.fo2VarSubstitution._
import at.logic.transformations.ceres.clauseSchema._
import at.logic.transformations.ceres.clauseSchema.resolutionDeduction._
import at.logic.transformations.ceres.clauseSchema.ResDeductionToLKTree._

@RunWith(classOf[JUnitRunner])
class resolutionSchemataTest extends SpecificationWithJUnit {
  private class MyParser extends StringReader("")
  "resolutionSchemataTest" should {
    "check the correctness of the resolution schemata" in {

      println(Console.YELLOW+"\n\n-------- integration tests, resolution schema --------\n\n"+Console.RESET)
      println("\n\n")
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
      val map = Map[Var, HOLExpression]() + Pair(k.asInstanceOf[Var], three) + Pair(l.asInstanceOf[Var], Succ(three))
      val subst = new SchemaSubstitution3(map)

      val sig1 = subst(trsSigma.map.get("σ'").get._2._1)
      println("\n\nsig1 = "+sig1)
      val sigma13 = unfoldSTermN(sig1, trsSigma)
      println("\n\nsigma13 = "+sigma13)
      val f = HOLApp(P, sig1).asInstanceOf[HOLFormula]
      val Psig1 = unfoldGroundAtom(f, trsSigma)
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
      resolutionProofSchemaDB.clear
      resolutionProofSchemaDB.add("ρ", Pair(rhoBase, rwBase), Pair(rhoStep, rwStep))
      println(Console.BOLD+"\nresolution-rewriting system:\n\n"+Console.RESET+resolutionProofSchemaDB.map )
      val base = resolutionProofSchemaDB.map.get("ρ").get._1._2
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
      println("\n")

      println("\n\n\ntransofrmation to tree:\n")
      val t = ResDeductionToLKTree(fo2sub)
      printSchemaProof(t)
//      Main.display("resolution tree ", t);
//      while(true){}
      println("\n\n\n")
      t.root must beEqualTo (Sequent(Nil, Nil))
      //      resolutionDeduction(r) must beEqualTo (nonVarSclause(Pa::Nil, Pb::Nil))
      ok
    }
  }
}
