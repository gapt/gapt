package at.logic.algorithms.cutIntroduction

import at.logic.language.fol._
import at.logic.parsing.language.prover9.Prover9TermParserLadrStyle.parseTerm
import SipGrammar._
import at.logic.provers.maxsat.{ MaxSATSolver, MaxSAT }

import org.specs2.mutable._

class SipTests extends Specification {
  "SipGrammar" should {
    "produce instance grammars" in {
      if ( !new MaxSAT( MaxSATSolver.ToySolver ).isInstalled ) skipped( "toysolver not installed" )

      val g = SipGrammar( Seq( tau -> Function( "r", List( nu ) ) ) )
      g.instanceGrammar( 2 ).productions.toSet must beEqualTo( Set( tau -> parseTerm( "r(0)" ), tau -> parseTerm( "r(s(0))" ) ) )
    }
  }

  "findMinimalSipGrammar" should {
    "find a grammar" in {
      if ( !new MaxSAT( MaxSATSolver.ToySolver ).isInstalled ) skipped( "toysolver not installed" )

      val lang = Seq( "r(0)", "r(s(0))" ) map parseTerm
      val g = findMinimalSipGrammar( Seq( ( 2, lang ) ) )
      g.productions.toSet must beEqualTo( Set(
        tau -> Function( "r", List( gamma ) ),
        gamma -> Function( "s", List( gamma ) ),
        gammaEnd -> FOLConst( "0" ) ) )
    }
  }
}