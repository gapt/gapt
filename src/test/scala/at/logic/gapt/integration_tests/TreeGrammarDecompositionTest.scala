package at.logic.gapt.integration_tests

import at.logic.gapt.examples.LinearExampleProof
import at.logic.gapt.expr.fol.FOLSubstitution
import at.logic.gapt.proofs.lk.cutIntroduction._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.lk.base.LKProof
import at.logic.gapt.expr._
import at.logic.gapt.provers.maxsat.MaxSat4j
import org.specs2.mutable._

/**
 * Created by spoerk on 09.10.14.
 */

class TreeGrammarDecompositionTest extends Specification {

  private def toTerms( p: LKProof ): List[FOLTerm] = {
    val testtree = LKToExpansionProof( p )
    val testterms = TermsExtraction( testtree )
    val testlanguage = testterms.set
    testlanguage
  }

  "TreeGrammarDecomposition" should {
    "extract and decompose the termset of the linear example proof of 8 (n = 1)" in {
      val proof = LinearExampleProof( 8 )
      val proofLanguage = toTerms( proof )

      val grammar = TreeGrammarDecomposition( proofLanguage, 1, MCSMethod.MaxSAT, new MaxSat4j() ).get

      // check size
      grammar.nonTerminals.size shouldEqual 2

      // check validity
      proofLanguage.toSet diff grammar.language must beEmpty
    }

    "extract and decompose the termset of the linear example proof of 18 (n = 2)" in {
      skipped( "this takes too long" )
      val proof = LinearExampleProof( 18 )
      val proofLanguage = toTerms( proof )

      val grammar = TreeGrammarDecomposition( proofLanguage, 2, MCSMethod.MaxSAT, new MaxSat4j() ).get

      // check size
      grammar.nonTerminals.size shouldEqual 3

      // check validity
      proofLanguage.toSet diff grammar.language must beEmpty
    }

  }
}

