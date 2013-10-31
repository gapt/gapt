package at.logic.transformations.ceres.ACNF

import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import org.specs2.mutable.SpecificationWithJUnit
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import java.io.{FileInputStream, InputStreamReader}
import at.logic.calculi.slk.SchemaProofDB
import java.io.File.separator
import java.io.IOException
import scala.io._
import at.logic.language.lambda.typedLambdaCalculus.{LambdaExpression, Var}
import at.logic.language.hol.HOLAbs._
import at.logic.language.hol.HOLVar._
import at.logic.language.lambda.types.Ti._
import at.logic.language.lambda.types.Ti
import at.logic.language.schema.sTerm._
import at.logic.algorithms.shlk._
import at.logic.calculi.lk.base.{LKProof, Sequent}
import at.logic.language.hol.{HOLFormula, HOLVar, HOLAbs, HOLExpression}
import at.logic.transformations.ceres.clauseSchema._
import org.specs2.internal.scalaz.Success
import at.logic.parsing.language.prover9.{Prover9TermParserLadrStyle, Prover9TermParser}
import at.logic.language.fol.{FOLExpression, AllVar, FOLConst, FOLVar}
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.lambda.substitutions.Substitution
import at.logic.transformations.ceres.struct.StructCreators
import at.logic.transformations.ceres.clauseSets.StandardClauseSet
import at.logic.provers.prover9.Prover9
import at.logic.transformations.ceres.projections.Projections
import at.logic.algorithms.resolution.RobinsonToLK
import at.logic.parsing.calculus.xml.saveXML

@RunWith(classOf[JUnitRunner])
class ACNFTest extends SpecificationWithJUnit {
  implicit val factory = defaultFormulaOccurrenceFactory

  sequential
  "ACNFTest" should {
    "should create correctly the ACNF for journal_example.lks" in {
      //println(Console.BLUE+"\n\n\n\n------- ACNF for the journal example instance  > 0 ------- \n\n"+Console.RESET)
      val s1 = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "journal_example.lks"))
      val s2 = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "resSchema1.rs"))
      val map = sFOParser.parseProof(s1)
      ParseResSchema(s2)
      val p = ACNF("\\varphi", "\\rho_1", 2)
//      printSchemaProof(p)
      //println("\n\n--- END ---\n\n")
      ok
    }

    //TODO: fix it ! The problem is that it needs cloning before plugging in a projection into the skeleton resolution proof.
//
//    "should create correctly the ACNF for journal_example.lks" in {
//      //println(Console.BLUE+"\n\n\n\n------- ACNF for the journal example instance = 0 ------- \n\n"+Console.RESET)
//      val s1 = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "journal_example.lks"))
//      val s2 = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "resSchema1.rs"))
//      val map = sFOParser.parseProof(s1)
//      ParseResSchema(s2)
//      val p = ACNF("\\varphi", "\\rho_1", 0)
////      printSchemaProof(p)
//      //println("\n\n--- END ---\n\n")
//      ok
//    }

    "should create correctly the ACNF for sEXP.lks" in {
      //println(Console.BLUE+"\n\n\n\n------- ACNF for the sEXP instance > 0 ------- \n\n"+Console.RESET)
      val s1 = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "sEXP.lks"))
      val s2 = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "resSchema_sEXP.rs"))
      val map = sFOParser.parseProof(s1)
      ParseResSchema(s2)
      val p = ACNF("\\psi", "\\rho_1", 1)
//      printSchemaProof(p)

//      val pair = InstantiateResSchema.getCorrectTermAndSubst("\\rho_1",1)
//      val rho1step1 = IntVarSubstitution(pair._1, pair._2)
//      val r = unfoldResolutionProofSchema2(rho1step1)
//      println("r = "+r)
//
//      val mapfo2 = Map[fo2Var, LambdaExpression]() + fo2SubstDB.map.head
//      val fo2sub = fo2VarSubstitution(r, mapfo2).asInstanceOf[sResolutionTerm]
////      val proof = ResDeductionToLKTree(fo2sub)
//      println("\n\nfo2sub = "+fo2sub)
      //println("\n\n--- END ---\n\n")
      ok
    }

    "should create correctly the ACNF for sEXP.lks" in {
      //println(Console.BLUE+"\n\n\n\n------- ACNF for the sEXP instance = 0 ------- \n\n"+Console.RESET)
      val s1 = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "sEXP.lks"))
      val s2 = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "resSchema_sEXP.rs"))
      val map = sFOParser.parseProof(s1)
      ParseResSchema(s2)
      val p = ACNF("\\psi", "\\rho_1", 0)
      //      printSchemaProof(p)
      //println("\n\n--- END ---\n\n")
      ok
    }

    "chould correctly handle equality rules" in {
      // checks if the execution of prover9 works ok, o.w. skips test
      Prover9.refute(List()) must not(throwA[IOException]).orSkip

      def groundproj(projections: Set[LKProof], groundSubs: List[(HOLVar, HOLExpression)]): Set[LKProof] = {
        groundSubs.map(subs => projections.map(pr => renameIndexedVarInProjection(pr, subs))).flatten.toSet
      }

      import at.logic.calculi.lk.propositionalRules._
      import at.logic.calculi.lk.equationalRules._
      import at.logic.calculi.lk.quantificationRules._
      val List(uv,fuu,fuv,ab,fab) = List("u = v", "f(u)=f(u)", "f(u)=f(v)", "a=b", "f(a)=f(b)") map (Prover9TermParserLadrStyle.parseFormula)
      val List(uy,xy,ay) = List("(all y (u = y -> f(u) = f(y)))",
                                "(all x all y (x = y -> f(x) = f(y)))",
                                "(all y (a = y -> f(a) = f(y)))") map (Prover9TermParserLadrStyle.parseFormula)
      val List(u,v) = List("u","v").map(s => FOLVar(VariableStringSymbol(s)))
      val List(a,b) = List("a","b").map(s => FOLConst(ConstantStringSymbol(s)))
      val ax1 = Axiom(List(uv),List(uv))
      val ax2 = Axiom(List(),List(fuu))
      val ax3 = Axiom(List(ab),List(ab))
      val ax4 = Axiom(List(fab),List(fab))

      val i1 = EquationRight1Rule(ax1,ax2,ax1.root.succedent(0),ax2.root.succedent(0), fuv)
      val i2 = ImpRightRule(i1, i1.root.antecedent(0),i1.root.succedent(0))
      println(i2.root)
      val i3 = ForallRightRule(i2, i2.root.succedent(0), uy, v )
      val i4 = ForallRightRule(i3, i3.root.succedent(0), xy, u )

      val i5 = ImpLeftRule(ax3,ax4,ax3.root.succedent(0),ax4.root.antecedent(0))
      val i6 = ForallLeftRule(i5, i5.root.antecedent(1),ay, b)
      val i7 = ForallLeftRule(i6, i6.root.antecedent(1),xy, a)

      val es = CutRule(i4,i7,i4.root.succedent(0),i7.root.antecedent(1))

      val cs = StandardClauseSet.transformStructToClauseSet(StructCreators.extract(es))
      println(cs)

      val rp = Prover9.refute(cs.toList.map(_.toFSequent))
      rp must not beEmpty

      //println(rp.get)

      val proj = Projections(es)
      proj must not beEmpty

      for (p <- proj) println(p)
      val rlkp = RobinsonToLK(rp.get)
      println(rlkp)
      val gproj = proj map (SubstituteProof(_, Substitution[HOLExpression]((u,b))))
      gproj map (x => println(" "+x))
      val acnf = ACNF.plugProjections(rlkp, gproj, es.root.toFSequent)
      println(acnf)

//      saveXML(List(("cutproof",es),("acnf",acnf)), List(("ccs",cs.map(_.toFSequent))), "equationacnf.xml")


      true must beEqualTo(true)
    }
  }
}

