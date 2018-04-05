package gapt.cutintro
import gapt.expr._
import gapt.proofs.{ Context, Sequent }
import gapt.proofs.gaptic._
import gapt.proofs.gaptic.{ Lemma, guessLabels, tactics }
import gapt.proofs.gaptic.tactics._
import gapt.proofs.lk.LKProof

/**
 * Constructs a proof for a given schematic Pi2-grammar if a cut formula exists
 */
object proveWithPi2Cut {

  /**
   * Constructs a proof for a given schematic Pi2-grammar if a cut formula exists
   * @param endSequent A provable Sequent for which the method builds a proof with Pi2-cut
   * @param seHs The given schematic Pi2-grammar
   * @param nameOfExistentialVariable The user can name the existential variable of the cut formula.
   *                                  (Default = xCut; In case the name is already taken
   *                                  the method looks for a similar name)
   * @param nameOfUniversalVariable The user can name the universal variable of the cut formula.
   *                                (Default = yCut; In case the name is already taken
   *                                the method looks for a similar name)
   * @return Optiontype that contains a proof with Pi2-cut if a Pi2-cut formula exists
   */
  def apply(
    endSequent:                Sequent[Formula],
    seHs:                      Pi2SeHs,
    nameOfExistentialVariable: Var              = fov"yCut",
    nameOfUniversalVariable:   Var              = fov"xCut" ): ( Option[LKProof] ) = {

    val ( cutFormulaWithoutQuantifiers: Option[Formula], nameOfExVa: Var, nameOfUnVa: Var ) =
      introducePi2Cut( seHs, nameOfExistentialVariable, nameOfUniversalVariable )

    cutFormulaWithoutQuantifiers match {
      case Some( t ) => giveProof( t, seHs, endSequent, nameOfExVa, nameOfUnVa )
      case None => {
        println( "No cut formula has been found." )
        None
      }
    }
  }

  /**
   * The construction of the proof itself
   * @param cutFormulaWithoutQuantifiers The quantifier-free cut formula
   *                                     that corresponds to the schematic Pi2-grammar
   * @param seHs The given schematic Pi2-grammar
   * @param endSequent A provable Sequent for which the method builds a proof with Pi2-cut
   * @param nameOfExVa Name of the existential variable of the cut-formula
   * @param nameOfUnVa Name of the universal variable of the cut-formula
   * @return Optiontype that contains a proof with Pi2-cut
   */
  def giveProof(
    cutFormulaWithoutQuantifiers: Formula,
    seHs:                         Pi2SeHs,
    endSequent:                   Sequent[Formula],
    nameOfExVa:                   Var,
    nameOfUnVa:                   Var ): ( Option[LKProof] ) = {

    var state = ProofState( endSequent )
    state += cut( "Cut", All( nameOfUnVa, Ex( nameOfExVa, cutFormulaWithoutQuantifiers ) ) )
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
