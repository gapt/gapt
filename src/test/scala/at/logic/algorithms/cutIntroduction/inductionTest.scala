package at.logic.algorithms.cutIntroduction

import at.logic.language.fol._
import at.logic.parsing.language.prover9.Prover9TermParserLadrStyle.parseTerm
import SipGrammar._
import at.logic.provers.maxsat.{ MaxSATSolver, MaxSAT }

import org.specs2.mutable._

class SipTests extends Specification {
  "SipGrammar" should {
    "produce instance grammars" in {
      if ( !new MaxSAT( MaxSATSolver.ToySAT ).isInstalled ) skipped( "ToySAT is not installed" )

      val g = SipGrammar( Seq( tau -> Function( "r", List( nu ) ) ) )
      g.instanceGrammar( 2 ).productions.toSet must beEqualTo( Set( tau -> parseTerm( "r(0)" ), tau -> parseTerm( "r(s(0))" ) ) )
    }
  }

  "findMinimalSipGrammar" should {
    "find a grammar" in {
      if ( !new MaxSAT( MaxSATSolver.ToySAT ).isInstalled ) skipped( "ToySAT is not installed" )

      val n = 5
      // r(0), ..., r(s^n(0))
      val lang = ( 0 until n ) map { i => Function( "r", List( Utils.numeral( i ) ) ) }
      val g = findMinimalSipGrammar( Seq( ( n, lang ) ) )
      g.productions must beEqualTo( Seq(
        tau -> Function( "r", List( nu ) ) ) )
    }
  }
}