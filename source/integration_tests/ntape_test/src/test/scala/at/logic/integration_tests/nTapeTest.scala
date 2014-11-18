package at.logic.integration_tests

import java.io.{File, IOException}

import at.logic.algorithms.fol.hol2fol.{replaceAbstractions, reduceHolToFol}
import at.logic.algorithms.hlk.HybridLatexParser
import at.logic.algorithms.lk.{AtomicExpansion, regularize}
import at.logic.algorithms.resolution.RobinsonToRal
import at.logic.algorithms.rewriting.DefinitionElimination
import at.logic.calculi.lksk.sequentToLabelledSequent
import at.logic.language.hol._

import at.logic.provers.prover9._
import at.logic.transformations.ceres.clauseSets.StandardClauseSet
import at.logic.transformations.ceres.projections.Projections
import at.logic.transformations.ceres.struct.StructCreators

import at.logic.transformations.ceres.{ceres_omega, CERES, CERESR2LK}
import at.logic.transformations.skolemization.lksk.LKtoLKskc

import org.junit.runner.RunWith
import org.specs2.mutable.SpecificationWithJUnit
import org.specs2.runner.JUnitRunner

@RunWith(classOf[JUnitRunner])
class nTapeTest extends SpecificationWithJUnit {
  val box = List()
  def checkForProverOrSkip = Prover9.refute(box) must not(throwA[IOException]).orSkip

  "The higher-order tape proof" should {
    "extract a struct from the preprocessed proof" in {
      checkForProverOrSkip

      val tokens = HybridLatexParser.parseFile("target" + File.separator + "test-classes" + File.separator + "tape3.llk")
      val pdb = HybridLatexParser.createLKProof(tokens)
      val elp = AtomicExpansion(DefinitionElimination(pdb.Definitions, regularize(pdb.proof("TAPEPROOF"))))
      val selp = LKtoLKskc(elp)

      val struct = StructCreators.extract(selp, x => containsQuantifier(x) || freeHOVariables(x).nonEmpty)
      val proj = Projections(selp, x => containsQuantifier(x) || freeHOVariables(x).nonEmpty)

      val cl = StandardClauseSet.transformStructToClauseSet(struct).map(_.toFSequent)
      val (cmap, folcl_) = replaceAbstractions(cl)
      val folcl = reduceHolToFol(folcl_)
      folcl.map(println(_))

      Prover9.refute(folcl) match {
        case None =>
          ko("could not refute clause set")
        case Some(rp) =>
          val ralp = RobinsonToRal(rp)
          val acnf = ceres_omega(proj, ralp, sequentToLabelledSequent(selp.root), struct)

          ok
      }

    }
  }

}
