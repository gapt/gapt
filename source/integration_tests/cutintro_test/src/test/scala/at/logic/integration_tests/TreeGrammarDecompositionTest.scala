package at.logic.integration_tests

import at.logic.algorithms.cutIntroduction._
import at.logic.calculi.lk._
import at.logic.calculi.lk.base.LKProof
import at.logic.language.fol._
import at.logic.transformations.herbrandExtraction.extractExpansionTrees
import at.logic.provers.maxsat.{MaxSAT, MaxSATSolver}
import org.junit.runner.RunWith
import org.specs2.runner.JUnitRunner
import org.specs2.mutable.SpecificationWithJUnit


/**
 * Created by spoerk on 09.10.14.
 */

@RunWith(classOf[JUnitRunner])
class TreeGrammarDecompositionTest extends SpecificationWithJUnit {

  private def LinearExampleProof(k: Int, n: Int): LKProof = {
    val s = "s"
    val c = "0"
    val p = "P"

    val x = FOLVar("x")
    val ass = AllVar(x, Imp(Atom(p, x :: Nil), Atom(p, Function(s, x :: Nil) :: Nil)))
    if (k == n) {// leaf proof {
      val a = Atom(p, Utils.numeral(n) :: Nil)
      WeakeningLeftRule(Axiom(a :: Nil, a :: Nil), ass)
    }
    else {
      val p1 = Atom(p, Utils.numeral(k) :: Nil)
      val p2 = Atom(p, Utils.numeral(k + 1) :: Nil)
      val aux = Imp(p1, p2)
      ContractionLeftRule(ForallLeftRule(ImpLeftRule(Axiom(p1 :: Nil, p1 :: Nil), LinearExampleProof(k + 1, n), p1, p2), aux, ass, Utils.numeral(k)), ass)
    }
  }

  private def toTerms(p: LKProof): List[FOLTerm] = {
    val testtree = extractExpansionTrees(p, false)
    val testterms = TermsExtraction(testtree)
    val testlanguage = testterms.set
    testlanguage
  }

  private def reconstructLanguage(grammar: Grammar): List[FOLTerm] = {
    if (grammar.size > 0) {
      val substitutions = grammar.slist.foldRight(List[Set[Substitution]]())((stuple, acc) => {
        val evs = stuple._1
        val substitutionSet = stuple._2.map(termVector => Substitution(evs.zip(termVector)))
        substitutionSet :: acc
      })
      //println("Substitutions: \n" + substitutions)
      // substitute everything
      substitutions.foldLeft(grammar.u)((u, subs) => {
        u.map(uterm => subs.map(sub => sub(uterm)).toList.distinct).toList.flatten.distinct
      })
    }
    else {
      Nil
    }
  }

  "TreeGrammarDecomposition" should {
    "extract and decompose the termset of the linear example proof of 8 (n = 1)" in {
      if (!(new MaxSAT(MaxSATSolver.QMaxSAT)).isInstalled()) skipped("MaxSAT is not installed")
      
      val proof = LinearExampleProof(0, 8)
      val proofLanguage = toTerms(proof)

      val grammar = TreeGrammarDecomposition(proofLanguage, 1, MCSMethod.MaxSAT)

      // check size
      grammar.slist.size shouldEqual 1

      // check validity
      val grammarLanguage = reconstructLanguage(grammar)

      proofLanguage diff grammarLanguage must beEmpty
    }

    "extract and decompose the termset of the linear example proof of 18 (n = 2)" in {
      if (!(new MaxSAT(MaxSATSolver.QMaxSAT)).isInstalled()) skipped("MaxSAT is not installed")
      skipped("this takes too long")
      val proof = LinearExampleProof(0, 18)
      val proofLanguage = toTerms(proof)

      val grammar = TreeGrammarDecomposition(proofLanguage, 2, MCSMethod.MaxSAT)

      // check size
      grammar.slist.size shouldEqual 2

      // check validity
      val grammarLanguage = reconstructLanguage(grammar)

      proofLanguage diff grammarLanguage must beEmpty
    }


  }
}


