package at.logic.integration_tests

import java.io.{File, IOException}

import at.logic.algorithms.fol.hol2fol.{replaceAbstractions, reduceHolToFol}
import at.logic.algorithms.fol.recreateWithFactory
import at.logic.algorithms.hlk.HybridLatexParser
import at.logic.algorithms.lk.{AtomicExpansion, regularize}
import at.logic.algorithms.resolution.RobinsonToRal
import at.logic.algorithms.rewriting.DefinitionElimination
import at.logic.calculi.lksk.sequentToLabelledSequent
import at.logic.language.hol._
import at.logic.language.lambda.{Substitution => LambdaSubstitution, LambdaExpression, Var}

import at.logic.provers.prover9._
import at.logic.transformations.ceres.clauseSets.{AlternativeStandardClauseSet, StandardClauseSet}
import at.logic.transformations.ceres.projections.Projections
import at.logic.transformations.ceres.struct.StructCreators

import at.logic.transformations.ceres.{ceres_omega, CERES, CERESR2LK}
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

  case class Robinson2RalAndUndoHOL2Fol(cmap : replaceAbstractions.ConstantsMap) extends RobinsonToRal {
    override def convert_formula(e:HOLFormula) : HOLFormula =
      recreateWithFactory(e,HOLFactory).asInstanceOf[HOLFormula]
    override def convert_substitution(s:Substitution) : Substitution = {
      recreateWithFactory(s, HOLFactory, convert_map).asInstanceOf[Substitution]
    }

    //TODO: this is somehow dirty....
    def convert_map(m : Map[Var,LambdaExpression]) : LambdaSubstitution =
      Substitution(m.asInstanceOf[Map[HOLVar,HOLExpression]])
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
      val folcl = reduceHolToFol(folcl_)
      folcl.map(println(_))

      show("Refuting clause set")
      Prover9.refute(folcl) match {
        case None =>
          ko("could not refute clause set")
        case Some(rp) =>
          show("Converting to Ral")
          val myconverter = Robinson2RalAndUndoHOL2Fol(cmap)
          val ralp = myconverter(rp)
          show("Creating acnf")
          //val acnf = ceres_omega(proj, ralp, sequentToLabelledSequent(selp.root), struct)

          ok
      }

    }
  }

}
