package at.logic.gapt.proofs.gaptic.tactics

import at.logic.gapt.expr._
import at.logic.gapt.proofs.gaptic.{ OpenAssumption, ProofState, Tactic, Tactical }
import at.logic.gapt.proofs.{ Ant, SequentIndex, Suc }

/**
 * Repeatedly applies unary rules that are unambiguous
 */
case object DecomposeTactic extends Tactical {
  def apply( proofState: ProofState ) = {
    RepeatTactic(
      AndLeftTactic() orElse
        OrRightTactic() orElse
        ImpRightTactic() orElse
        ForallRightTactic() orElse
        ExistsLeftTactic()
    )( proofState )
  }
}

case class DestructTactic( applyToLabel: Option[String] = None ) extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    def canDestruct( formula: HOLFormula, index: SequentIndex ): Boolean = ( formula, index ) match {
      case ( All( _, _ ), Suc( _ ) ) => true
      case ( Ex( _, _ ), Ant( _ ) )  => true
      case ( And( _, _ ), _ )        => true
      case ( Or( x, y ), _ )         => true
      case ( Imp( x, y ), _ )        => true
      case ( Neg( _ ), _ )           => true
      case _                         => false
    }

    val indices = applyToLabel match {
      case None =>
        for ( ( ( _, formula ), index ) <- goalSequent.zipWithIndex.elements if canDestruct( formula, index ) )
          yield index

      case Some( label ) =>
        for ( ( ( `label`, _ ), index ) <- goalSequent.zipWithIndex.elements )
          yield index
    }

    // Select some formula index!
    indices.headOption match {
      case Some( i ) =>
        val ( existingLabel, _ ) = goalSequent( i )

        val tac = ForallRightTactic( applyToLabel = existingLabel ) orElse
          ExistsLeftTactic( applyToLabel = existingLabel ) orElse
          AndLeftTactic( applyToLabel = existingLabel ) orElse
          AndRightTactic( applyToLabel = existingLabel ) orElse
          OrLeftTactic( applyToLabel = existingLabel ) orElse
          OrRightTactic( applyToLabel = existingLabel ) orElse
          ImpLeftTactic( applyToLabel = existingLabel ) orElse
          ImpRightTactic( applyToLabel = existingLabel ) orElse
          NegLeftTactic( applyToLabel = existingLabel ) orElse
          NegRightTactic( applyToLabel = existingLabel )

        tac( goal )
      case None => None
    }
  }
}

/**
 * Companion object for DestructTactic
 */
object DestructTactic {
  def apply( applyToLabel: String ) = new DestructTactic( Some( applyToLabel ) )
}

