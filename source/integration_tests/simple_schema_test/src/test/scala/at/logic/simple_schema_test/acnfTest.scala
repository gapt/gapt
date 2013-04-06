package at.logic.simple_schema_test

import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import org.specs2.mutable.SpecificationWithJUnit
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.calculi.occurrences.{FormulaOccurrence, defaultFormulaOccurrenceFactory}
import java.io.{FileInputStream, InputStreamReader}
import at.logic.calculi.slk.SchemaProofDB
import java.io.File.separator
import scala.io._
import at.logic.gui.prooftool.gui.Main
import at.logic.language.lambda.typedLambdaCalculus.{LambdaExpression, Var}
import at.logic.language.hol.HOLAbs._
import at.logic.language.hol.HOLVar._
import at.logic.language.lambda.types.Ti._
import at.logic.language.lambda.types.Ti
import at.logic.language.schema.sTerm._
import at.logic.algorithms.shlk._
import at.logic.calculi.lk.base.{FSequent, Sequent}
import at.logic.language.hol._
import at.logic.transformations.ceres.clauseSchema._
import at.logic.transformations.ceres.ACNF._
import at.logic.gui.prooftool.gui.Main
import at.logic.transformations.ceres.struct.StructCreators
import at.logic.provers.prover9.Prover9
import at.logic.calculi.resolution.robinson.RobinsonResolutionProof
import at.logic.algorithms.resolution.RobinsonToLK
import at.logic.parsing.language.tptp.TPTPFOLExporter
import at.logic.transformations.ceres.projections.Projections
import at.logic.calculi.treeProofs.BinaryTreeProof
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.schema.{IntZero, indexedFOVar}
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.lambda.types.Ti
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.schema.IntZero

@RunWith(classOf[JUnitRunner])
class ACNFTest extends SpecificationWithJUnit {
  implicit val factory = defaultFormulaOccurrenceFactory
  "ACNFTest" should {
    "should parse correctly the Resolution schema for journal_example.lks" in {
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

//    "should create correctly the ACNF for journal_example.lks" in {
//      //println(Console.BLUE+"\n\n\n\n------- ACNF for the journal example instance = 0 ------- \n\n"+Console.RESET)
//      val s1 = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "journal_example.lks"))
//      val s2 = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "resSchema1.rs"))
//      val map = sFOParser.parseProof(s1)
//      ParseResSchema(s2)
//      val p = ACNF("\\varphi", "\\rho_1", 0)
//      //printSchemaProof(p)
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

    "should refute (using Prover9) the clause set for a given instance of sEXP.lks" in {
      println(Console.BLUE+"\n\n\n\n------- sEXP instance = 1 for prover 9  ------- \n\n"+Console.RESET)
      val s1 = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "sEXP.lks"))
      val s2 = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "resSchema_sEXP.rs"))
      val map = sFOParser.parseProof(s1)
      ParseResSchema(s2)
      val p = ACNF("\\psi", "\\rho_1", 0)

      val psi2 = applySchemaSubstitution2("\\psi", 2)
//      Main.display("psi2", psi2) ; while(true){}

      val struct = StructCreators.extract( psi2 )
      val listOfSeqs = at.logic.transformations.ceres.clauseSets.StandardClauseSet.transformStructToClauseSet(struct)
//      Main.display("listOfSeqs", listOfSeqs) ; while(true){}

      val listOfFClauses = listOfSeqs.map(seq => seq.toFSequent()).map(fseq => FSequent(fseq.antecedent.map(f => TPTPFOLExporter.hol2fol(f)) , fseq.succedent.map(f => TPTPFOLExporter.hol2fol(f)) ))
//      Main.display("listOfFClauses", listOfFClauses) ; while(true){}

      val robinsonResProof: Option[RobinsonResolutionProof] = Prover9.refute(listOfSeqs.map(seq => seq.toFSequent))
//      Main.display("robinsonResProof", robinsonResProof.get) ; while(true){}
      val subs: List[(HOLVar, HOLExpression)] = getInstantiationsOfTheIndexedFOVars(robinsonResProof.get)
      println("\nsubs = "+subs)

      val robToLK = RobinsonToLK(robinsonResProof.get)
//      Main.display("robToLK", robToLK) ; while(true){}
      val robToLKToHOL = ConvertCutsToHOLFormulasInResProof(robToLK)
//      Main.display("robToLKToHOL", robToLKToHOL) ; while(true){}

      val proj_set = Projections(psi2)
//      Main.display("projection", proj_set.tail.tail.head) ; while(true){}

      val set = subs.map(subs => proj_set.map(pr => renameIndexedVarInProjection(pr, subs))).flatten.toSet
      println("\nset = "+set.size)
      val seqs = set.map(s => s.root)
//      Main.display("seqs", seqs) ; while(true){}

      val acnf2 = ACNF(robToLKToHOL, set, psi2.root.toFSequent())
//      Main.display("acnf2", acnf2) ; while(true){}

      println("\n\n--- END ---\n\n")
      ok
    }




//    "should refute (using Prover9) the clause set for a given instance of journal_example.lks" in {
//      println(Console.RED+"\n\n\n\n------- journal_example instance = 1 for prover 9  ------- \n\n"+Console.RESET)
//      val s1 = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "journal_example.lks"))
//      val s2 = new InputStreamReader(new FileInputStream("target" + separator + "test-classes" + separator + "resSchema_journal.rs"))
//      val map = sFOParser.parseProof(s1)
//      ParseResSchema(s2)
//      val p = ACNF("\\varphi", "\\rho_1", 0)
//
//      val varphi1 = applySchemaSubstitution2("\\varphi", 1)
////            Main.display("varphi1", varphi1) ; while(true){}
//
//      val struct = StructCreators.extract( varphi1 )
//      val listOfSeqs = at.logic.transformations.ceres.clauseSets.StandardClauseSet.transformStructToClauseSet(struct)
////            Main.display("listOfSeqs", listOfSeqs) ; while(true){}
//
//      val listOfFClauses = listOfSeqs.map(seq => seq.toFSequent()).map(fseq => FSequent(fseq.antecedent.map(f => TPTPFOLExporter.hol2fol(f)) , fseq.succedent.map(f => TPTPFOLExporter.hol2fol(f)) ))
////            Main.display("listOfFClauses", listOfFClauses) ; while(true){}
//
//      val robinsonResProof: Option[RobinsonResolutionProof] = Prover9.refute(listOfSeqs.map(seq => seq.toFSequent))
////            Main.display("robinsonResProof", robinsonResProof.get) ; while(true){}
////      getInstantiations(robinsonResProof.get)
//
//      val robToLK = RobinsonToLK(robinsonResProof.get)
////            Main.display("robToLK", robToLK) ; while(true){}
//      //      println("\nrobToLK:"+robToLK)
//
////      val proj_set = Projections(varphi1)
////      println("\nproj_set.size = "+proj_set.size)
////            Main.display("projection", proj_set.tail.tail.head) ; while(true){}
//
////      val setOfEndSeqs = proj_set.map(proj => proj.root)
////            Main.display("setOfEndSeqs", setOfEndSeqs) ; while(true){}
//
//      //      val acnf2 = ACNF(robToLK, proj_set, psi2.root.toFSequent())
//
//      println("\n\n--- END ---\n\n")
//      ok
//    }
  }
}

