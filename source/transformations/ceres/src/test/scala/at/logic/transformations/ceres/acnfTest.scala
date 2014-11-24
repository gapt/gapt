package at.logic.transformations.ceres.ACNF

import at.logic.algorithms.resolution.RobinsonToLK
import at.logic.algorithms.shlk._
import at.logic.calculi.lk._
import at.logic.calculi.lk.base.{LKProof, Sequent}
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import at.logic.calculi.slk.SchemaProofDB
import at.logic.language.fol.{Substitution => FOLSubstitution, FOLExpression, AllVar, FOLConst, FOLVar}
import at.logic.language.hol.{HOLFormula, HOLVar, HOLAbs, HOLExpression}
import at.logic.language.lambda.types._
import at.logic.parsing.language.prover9.Prover9TermParserLadrStyle
import at.logic.parsing.shlk_parsing.sFOParser
import at.logic.provers.prover9.Prover9
import at.logic.transformations.ceres.clauseSchema._
import at.logic.transformations.ceres.clauseSets.StandardClauseSet
import at.logic.transformations.ceres.projections.Projections
import at.logic.transformations.ceres.struct.StructCreators
import java.io.File.separator
import java.io.{FileInputStream, InputStreamReader}
import org.junit.runner.RunWith
//import org.specs2.internal.scalaz.Success
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner
import scala.io._
import at.logic.algorithms.lk.applySubstitution

@RunWith(classOf[JUnitRunner])
class acnfTest extends SpecificationWithJUnit {
  implicit val factory = defaultFormulaOccurrenceFactory

  args (skipAll = !Prover9.isInstalled ());

  sequential
  "ACNFTest" should {
    "should create correctly the ACNF for journal_example.lks" in {
      skipped("Error at: at.logic.transformations.ceres.clauseSchema.ResDeductionToLKTree$.apply(clauseSchema.scala:659)")

      val s1 = new InputStreamReader(getClass.getClassLoader.getResourceAsStream("ceres-journal_example.lks"))
      val s2 = new InputStreamReader(getClass.getClassLoader.getResourceAsStream("resSchema1.rs"))
      val map = sFOParser.parseProof(s1)
      ParseResSchema(s2)
      val p = ACNF("\\varphi", "\\rho_1", 2)
      ok
    }

    //TODO: fix it ! The problem is that it needs cloning before plugging in a projection into the skeleton resolution proof.
//
//    "should create correctly the ACNF for journal_example.lks" in {
//      //println(Console.BLUE+"\n\n\n\n------- ACNF for the journal example instance = 0 ------- \n\n"+Console.RESET)
//      val s1 = new InputStreamReader(getClass.getClassLoader.getResourceAsStream("ceres-journal_example.lks"))
//      val s2 = new InputStreamReader(getClass.getClassLoader.getResourceAsStream("resSchema1.rs"))
//      val map = sFOParser.parseProof(s1)
//      ParseResSchema(s2)
//      val p = ACNF("\\varphi", "\\rho_1", 0)
////      printSchemaProof(p)
//      //println("\n\n--- END ---\n\n")
//      ok
//    }

    "should create correctly the ACNF for sEXP.lks" in {
      skipped("Error at: at.logic.transformations.ceres.clauseSchema.ResDeductionToLKTree$.apply(clauseSchema.scala:659)")

      val s1 = new InputStreamReader(getClass.getClassLoader.getResourceAsStream("sEXP.lks"))
      val s2 = new InputStreamReader(getClass.getClassLoader.getResourceAsStream("resSchema_sEXP.rs"))
      val map = sFOParser.parseProof(s1)
      ParseResSchema(s2)
      val p = ACNF("\\psi", "\\rho_1", 1)
      ok
    }

    "should correctly handle equality rules" in {
      def groundproj(projections: Set[LKProof], groundSubs: List[(HOLVar, HOLExpression)]): Set[LKProof] = {
        groundSubs.map(subs => projections.map(pr => renameIndexedVarInProjection(pr, subs))).flatten.toSet
      }

      val List(uv,fuu,fuv,ab,fab) = List("u = v", "f(u)=f(u)", "f(u)=f(v)", "a=b", "f(a)=f(b)") map (Prover9TermParserLadrStyle.parseFormula)
      val List(uy,xy,ay) = List("(all y (u = y -> f(u) = f(y)))",
                                "(all x all y (x = y -> f(x) = f(y)))",
                                "(all y (a = y -> f(a) = f(y)))") map (Prover9TermParserLadrStyle.parseFormula)
      val List(u,v) = List("u","v").map(s => FOLVar(s))
      val List(a,b) = List("a","b").map(s => FOLConst(s))
      val ax1 = Axiom(List(uv),List(uv))
      val ax2 = Axiom(List(),List(fuu))
      val ax3 = Axiom(List(ab),List(ab))
      val ax4 = Axiom(List(fab),List(fab))

      val i1 = EquationRight1Rule(ax1,ax2,ax1.root.succedent(0),ax2.root.succedent(0), fuv)
      val i2 = ImpRightRule(i1, i1.root.antecedent(0),i1.root.succedent(0))
      val i3 = ForallRightRule(i2, i2.root.succedent(0), uy, v )
      val i4 = ForallRightRule(i3, i3.root.succedent(0), xy, u )

      val i5 = ImpLeftRule(ax3,ax4,ax3.root.succedent(0),ax4.root.antecedent(0))
      val i6 = ForallLeftRule(i5, i5.root.antecedent(1),ay, b)
      val i7 = ForallLeftRule(i6, i6.root.antecedent(1),xy, a)

      val es = CutRule(i4,i7,i4.root.succedent(0),i7.root.antecedent(1))

      val cs = StandardClauseSet.transformStructToClauseSet(StructCreators.extract(es))

      val rp = Prover9.refute(cs.toList.map(_.toFSequent))
      rp must not beEmpty


      val proj = Projections(es)
      proj must not beEmpty

      //for (p <- proj) println(p)
      val rlkp = RobinsonToLK(rp.get)
      val gproj = proj map (applySubstitution(_, FOLSubstitution((u,b)::Nil))._1)
      //gproj map (x => println(" "+x))
      val acnf = ACNF.plugProjections(rlkp, gproj, es.root.toFSequent)
      //println(acnf)

      true must beEqualTo(true)
    }
  }
}

