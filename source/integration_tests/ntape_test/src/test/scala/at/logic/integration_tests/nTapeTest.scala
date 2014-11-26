package at.logic.integration_tests

import java.io.{ IOException}

import at.logic.algorithms.fol.hol2fol.{undoHol2Fol, replaceAbstractions, reduceHolToFol}
import at.logic.algorithms.fol.recreateWithFactory
import at.logic.algorithms.hlk.HybridLatexParser
import at.logic.algorithms.lk.{AtomicExpansion, regularize}
import at.logic.algorithms.resolution.RobinsonToRal
import at.logic.algorithms.rewriting.DefinitionElimination
import at.logic.calculi.lk.base.LKProof
import at.logic.calculi.lksk.sequentToLabelledSequent
import at.logic.language.fol.{FOLVar, FOLFormula, FOLExpression}
import at.logic.language.hol._

import at.logic.provers.prover9._
import at.logic.transformations.ceres.clauseSets.AlternativeStandardClauseSet
import at.logic.transformations.ceres.projections.Projections
import at.logic.transformations.ceres.struct.StructCreators

import at.logic.transformations.ceres.ceres_omega
import at.logic.transformations.herbrandExtraction.lksk.extractLKSKExpansionTrees
import at.logic.transformations.skolemization.lksk.LKtoLKskc
import at.logic.utils.testing.ClasspathFileCopier

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class nTapeTest extends SpecificationWithJUnit with ClasspathFileCopier {
  val box = List()
  def checkForProverOrSkip = Prover9.refute(box) must not(throwA[IOException]).orSkip

  def show(s:String) = println("+++++++++ "+s+" ++++++++++")


  object Robinson2RalAndUndoHOL2Fol {
    def apply(sig_vars : Map[String, List[HOLVar]],
              sig_consts : Map[String, List[HOLConst]],
              cmap : replaceAbstractions.ConstantsMap) =
      new Robinson2RalAndUndoHOL2Fol(sig_vars, sig_consts, cmap)
  }


  class Robinson2RalAndUndoHOL2Fol(sig_vars : Map[String, List[HOLVar]],
                                   sig_consts : Map[String, List[HOLConst]],
                                   cmap : replaceAbstractions.ConstantsMap) extends RobinsonToRal {
    val absmap = Map[String, HOLExpression]() ++ (cmap.toList.map(x => (x._2.toString, x._1)))
    val cache = Map[HOLExpression, HOLExpression]()

    override def convert_formula(e:HOLFormula) : HOLFormula = {
      require(e.isInstanceOf[FOLFormula])
      recreateWithFactory(undoHol2Fol.backtranslate(e.asInstanceOf[FOLFormula], sig_vars, sig_consts, absmap)(HOLFactory), HOLFactory).asInstanceOf[HOLFormula]
    }

    override def convert_substitution(s:Substitution) : Substitution = {
      val mapping = s.map.toList.map(x =>
        (
          recreateWithFactory(undoHol2Fol.backtranslate(x._1.asInstanceOf[FOLVar], sig_vars, sig_consts, absmap, None)(HOLFactory), HOLFactory).asInstanceOf[HOLVar],
          recreateWithFactory(undoHol2Fol.backtranslate(x._2.asInstanceOf[FOLExpression], sig_vars, sig_consts, absmap, None)(HOLFactory), HOLFactory).asInstanceOf[HOLExpression]
          )
      )

      Substitution(mapping)
    }
  }


  "The higher-order tape proof" should {
    "extract a struct from the preprocessed proof" in {
      checkForProverOrSkip
      show("Loading file")
      val tokens = HybridLatexParser.parseFile(tempCopyOfClasspathFile("tape3.llk"))
      val pdb = HybridLatexParser.createLKProof(tokens)
      show("Eliminating definitions, expanding tautological axioms")
      val elp = AtomicExpansion(DefinitionElimination(pdb.Definitions, regularize(pdb.proof("TAPEPROOF"))))
      show("Skolemizing")
      val selp = LKtoLKskc(elp)

      show("Extracting struct")
      val struct = StructCreators.extract(selp, x => containsQuantifier(x) || freeHOVariables(x).nonEmpty)
      show("Computing projections")
      val proj = Projections(selp, x => containsQuantifier(x) || freeHOVariables(x).nonEmpty)

      show("Computing clause set")
      val cl = AlternativeStandardClauseSet(struct)
      show("Exporting to prover 9")
      val (cmap, folcl_) = replaceAbstractions(cl.toList)
      println("Calculated cmap: ")
      cmap.map(x => println(x._1+" := "+x._2))

      val folcl = reduceHolToFol(folcl_)
      folcl.map(println(_))

      show("Refuting clause set")
      Prover9.refute(folcl) match {
        case None =>
          ko("could not refute clause set")
        case Some(rp) =>
          show("Getting formulas")
          val proofformulas = selp.nodes.flatMap(_.asInstanceOf[LKProof].root.toFSequent.formulas  ).toList.distinct

          show("Extracting signature from "+proofformulas.size+ " formulas")
          val (sigc, sigv) = undoHol2Fol.getSignature( proofformulas )

          show("Converting to Ral")

          val myconverter = Robinson2RalAndUndoHOL2Fol(sigv.map(x => (x._1, x._2.toList)), sigc.map(x => (x._1, x._2.toList)), cmap)
          val ralp = myconverter(rp)
          show("Creating acnf")
          val (acnf, endclause) = ceres_omega(proj, ralp, sequentToLabelledSequent(selp.root), struct)
          show("Compute expansion tree")
          val et = extractLKSKExpansionTrees(acnf)
          show(" HOORAY! ")
          //println(et)

          ok
      }

    }
  }

}
