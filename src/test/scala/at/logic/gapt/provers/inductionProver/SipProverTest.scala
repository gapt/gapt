package at.logic.gapt.provers.inductionProver

import at.logic.gapt.expr.FOLVar
import at.logic.gapt.expr.fol.{ Utils, FOLSubstitution }
import at.logic.gapt.expr.hol.univclosure
import at.logic.gapt.proofs.{ Sequent, Suc, Ant }
import at.logic.gapt.proofs.expansionTrees.{ formulaToExpansionTree, ExpansionSequent }
import at.logic.gapt.proofs.lkNew.LKProver
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle.parseFormula
import SimpleInductionProof._
import at.logic.gapt.provers.sat.Sat4j
import org.specs2.mutable._

class SipProverTest extends Specification {

  "linear example from provided instance proofs" in {
    val endSequent = ( "P(0)" +: "P(x) -> P(s(x))" +: Sequent() :+ "P(x)" ).
      map( parseFormula ).
      map( univclosure( _ ), FOLSubstitution( FOLVar( "x" ) -> alpha ).apply )

    def instanceProof( n: Int ): ExpansionSequent = {
      val instP0 = formulaToExpansionTree( endSequent( Ant( 0 ) ), false )
      val instPs = formulaToExpansionTree(
        endSequent( Ant( 1 ) ),
        ( 0 until n ).toList map { i => FOLSubstitution( FOLVar( "x" ) -> Utils.numeral( i ) ) }, false
      )
      val instPa = formulaToExpansionTree( FOLSubstitution( alpha -> Utils.numeral( n ) )( endSequent( Suc( 0 ) ) ), true )
      instP0 +: instPs +: Sequent() :+ instPa
    }

    val tautP = Sat4j

    val sipProver = new SipProver(
      quasiTautProver = tautP,
      solutionFinder = new HeuristicSolutionFinder( 1, prover = tautP )
    )

    val Some( sip ) = sipProver.getSimpleInductionProof( endSequent, ( 0 until 5 ).map { n => n -> instanceProof( n ) } )

    tautP.isValid( sip.Sequent0 ) must_== true
    tautP.isValid( sip.Sequent1 ) must_== true
    tautP.isValid( sip.Sequent2 ) must_== true

    sip.toLKProof( LKProver )

    ok
  }

}
