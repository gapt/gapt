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

  private def reconstructLanguage( grammar: Grammar ): List[FOLTerm] = {
    if ( grammar.size > 0 ) {
      val substitutions = grammar.slist.foldRight( List[Set[FOLSubstitution]]() )( ( stuple, acc ) => {
        val evs = stuple._1
        val substitutionSet = stuple._2.map( termVector => FOLSubstitution( evs.zip( termVector ) ) )
        substitutionSet :: acc
      } )
      //println("Substitutions: \n" + substitutions)
      // substitute everything
      substitutions.foldLeft( grammar.u )( ( u, subs ) => {
        u.map( uterm => subs.map( sub => sub( uterm ) ).toList.distinct ).toList.flatten.distinct
      } )
    } else {
      Nil
    }
  }

  "TreeGrammarDecomposition" should {
    "extract and decompose the termset of the linear example proof of 8 (n = 1)" in {
      val proof = LinearExampleProof( 8 )
      val proofLanguage = toTerms( proof )

      val grammar = TreeGrammarDecomposition( proofLanguage, 1, MCSMethod.MaxSAT, new MaxSat4j() )

      // check size
      grammar.get.slist.size shouldEqual 1

      // check validity
      val grammarLanguage = reconstructLanguage( grammar.get )

      proofLanguage diff grammarLanguage must beEmpty
    }

    "extract and decompose the termset of the linear example proof of 18 (n = 2)" in {
      skipped( "this takes too long" )
      val proof = LinearExampleProof( 18 )
      val proofLanguage = toTerms( proof )

      val grammar = TreeGrammarDecomposition( proofLanguage, 2, MCSMethod.MaxSAT, new MaxSat4j() )

      // check size
      grammar.get.slist.size shouldEqual 2

      // check validity
      val grammarLanguage = reconstructLanguage( grammar.get )

      proofLanguage diff grammarLanguage must beEmpty
    }

  }
}

