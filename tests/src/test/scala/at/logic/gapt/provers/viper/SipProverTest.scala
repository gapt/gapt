package at.logic.gapt.provers.viper

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.Utils
import at.logic.gapt.proofs.{ Sequent, Suc, Ant }
import at.logic.gapt.proofs.expansion.{ ExpansionProof, formulaToExpansionTree }
import at.logic.gapt.proofs.lk.LKProver
import SimpleInductionProof._
import at.logic.gapt.provers.sat.Sat4j
import org.specs2.mutable._

class SipProverTest extends Specification {

  "linear example from provided instance proofs" in {
    val endSequent = fof"P(0)" +: fof"!x (P(x) -> P(s(x)))" +: Sequent() :+ fof"P($alpha)"

    def instanceProof( n: Int ): ExpansionProof = {
      val instP0 = formulaToExpansionTree( endSequent( Ant( 0 ) ), false )
      val instPs = formulaToExpansionTree(
        endSequent( Ant( 1 ) ),
        ( 0 until n ).toList map { i => FOLSubstitution( fov"x" -> Utils.numeral( i ) ) }, false
      )
      val instPa = formulaToExpansionTree( FOLSubstitution( alpha -> Utils.numeral( n ) )( endSequent( Suc( 0 ) ) ), true )
      ExpansionProof( instP0 +: instPs +: Sequent() :+ instPa )
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
