package at.logic.gapt.expr

import at.logic.gapt.proofs.{ Context, Sequent }
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.gaptic.{ Lemma, guessLabels, tactics }
import at.logic.gapt.proofs.gaptic.tactics._
import at.logic.gapt.proofs.lk.LKProof

/**
 * Created by root on 08.02.17.
 */
object proveWithPi2Cut {

  def apply(
    endSequent:                Sequent[FOLFormula],
    seHs:                      Pi2SeHs,
    nameOfExistentialVariable: FOLVar              = fov"yCut",
    nameOfUniversalVariable:   FOLVar              = fov"xCut"
  ): ( Option[LKProof] ) = {

    val ( cutFormulaWithoutQuantifiers: Option[FOLFormula], nameOfExVa: FOLVar, nameOfUnVa: FOLVar ) = introducePi2Cut( seHs, nameOfExistentialVariable, nameOfUniversalVariable )

    cutFormulaWithoutQuantifiers match {
      case Some( t ) => giveProof( t, seHs, endSequent, nameOfExVa, nameOfUnVa )
      case None => {
        println( "No cut formula has been found." )
        None
      }
    }
  }

  private def giveProof(
    cutFormulaWithoutQuantifiers: FOLFormula,
    seHs:                         Pi2SeHs,
    endSequent:                   Sequent[FOLFormula],
    nameOfExVa:                   FOLVar,
    nameOfUnVa:                   FOLVar
  ): ( Option[LKProof] ) = {

    //val listAnt: Seq[String] = ( for {
    //  i <- 0 until endSequent.antecedent.size
    //} yield i.toString )
    //val listSuc: Seq[String] = ( for {
    //  i <- endSequent.antecedent.size until endSequent.antecedent.size + endSequent.succedent.size
    //} yield i.toString ).toList

    var ctx = Context.default
    ctx += Context.Sort( "i" )
    for ( c <- constants( seHs.reducedRepresentation.antecedent ++: endSequent :++ seHs.reducedRepresentation.succedent ) ) ctx += c
    // for ( c <- constants( seHs.substitutionsForBetaWithAlpha ); if !ctx.contains( c.asInstanceOf ) ) ctx += c

    var state = ProofState( guessLabels( endSequent ) )
    state += cut( "Cut", fof"!$nameOfUnVa ?$nameOfExVa ($cutFormulaWithoutQuantifiers )" )
    state += allR( "Cut", seHs.universalEigenvariable )
    for ( t <- seHs.substitutionsForBetaWithAlpha ) { state += exR( "Cut", t ) }
    state += haveInstances( seHs.reducedRepresentation )
    state += prop
    for ( i <- 0 until seHs.multiplicityOfAlpha ) {
      state += allL( "Cut", seHs.substitutionsForAlpha( i ) )
      state += exL( "Cut_" + i.toString, seHs.existentialEigenvariables( i ) )
    }
    state += haveInstances( seHs.reducedRepresentation )
    state += prop
    val proof = state.result

    Some( proof )
  }

}
