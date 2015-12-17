package at.logic.gapt.proofs.gaptic

import at.logic.gapt.expr.HOLFormula
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.lk._

/**
 *
 * @param initGoal
 */
case class Lemma( initGoal: Sequent[( String, HOLFormula )], showOutput: Boolean = true ) {
  private var proofState = ProofState( 0, OpenAssumption( initGoal ) )

  if ( showOutput )
    printSubGoals()

  /**
   *
   * @param t
   */
  def use( t: Tactical ) = t( proofState ) match {
    case Some( newProofState ) =>
      // Replace proof state
      proofState = newProofState

      // Print new sub goals
      if ( showOutput )
        printSubGoals()
    case None =>
      // Tactic failure
      throw new TacticFailureException( "Failed to apply tactic " + t + " to proof state " + proofState )
  }

  /**
   *
   * @return
   */
  def qed(): LKProof = {
    if ( proofState.subGoals.isEmpty ) {
      // Done
      proofState.proofSegment
    } else {
      // Failure
      throw new QedFailureException( "Proof not completed. There are still " + proofState.subGoals.length + " unproved sub goals." )
    }
  }

  /**
   *
   */
  private def printSubGoals() = {
    if ( proofState.subGoals.isEmpty )
      println( "No current sub goals!" )
    else {
      println( "Current sub goals:" )
      for ( i <- proofState.subGoals.indices )
        println( s"$i: ${proofState.displaySubGoal( ( i ) )}" )
    }
  }
}

class TacticFailureException( s: String ) extends Throwable

class QedFailureException( s: String ) extends Throwable
