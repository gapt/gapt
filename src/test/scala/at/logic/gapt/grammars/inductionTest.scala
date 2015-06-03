package at.logic.gapt.grammars

import at.logic.gapt.expr._
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.parseTerm
import at.logic.gapt.grammars.SipGrammar._
import at.logic.gapt.language.fol.Utils
import at.logic.gapt.provers.maxsat.QMaxSAT
import org.specs2.mutable._

class SipTests extends Specification {
  "SipGrammar" should {
    "produce instance grammars" in {
      val g = SipGrammar( Seq( tau -> FOLFunction( "r", List( nu ) ) ) )
      g.instanceGrammar( 2 ).productions.toSet must beEqualTo( Set( tau -> parseTerm( "r(0)" ), tau -> parseTerm( "r(s(0))" ) ) )
    }

    "handle n=0 correctly" in {
      val g = SipGrammar( Seq(
        tau -> FOLFunction( "r", List( beta ) ),
        tau -> FOLFunction( "r", List( nu ) ),
        gamma -> gamma,
        gammaEnd -> parseTerm( "0" ) ) )
      g.instanceGrammar( 0 ).productions.toSet must beEqualTo( Set(
        tau -> parseTerm( "r(0)" ),
        tau -> FOLFunction( "r", List( gamma_i( 0 ) ) ),
        gamma_i( 0 ) -> parseTerm( "0" ) ) )
    }
  }

  "findMinimalSipGrammar" should {
    "find a grammar" in {
      val n = 5
      // r(0), ..., r(s^n(0))
      val lang = ( 0 until n ) map { i => FOLFunction( "tuple1", List( Utils.numeral( i ) ) ) }
      val g = findMinimalSipGrammar( Seq( ( n, lang ) ) )
      g.productions must beEqualTo( Seq(
        tau -> FOLFunction( "tuple1", List( nu ) ) ) )
    }

    "find a grammar covering multiple instance languages" in {
      if ( !new QMaxSAT().isInstalled )
        skipped( "does not work with maxsat4j -- wrong result..." )

      val n = 4
      // i |-> {r(0), ..., r(s^i(0))}
      val langs = ( 0 until n ) map { i =>
        ( i, ( 0 until i ) map { j =>
          FOLFunction( "tuple1", List( Utils.numeral( j ) ) )
        } )
      }
      val g = findMinimalSipGrammar( langs, new QMaxSAT )
      g.productions must beEqualTo( Seq(
        tau -> FOLFunction( "tuple1", List( nu ) ) ) )
    }

  }
}