package at.logic.gapt.proofs.gaptic.tactics

import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.provers.prover9.Prover9

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

        val tac = allR( existingLabel ) orElse
          exL( existingLabel ) orElse
          andL( existingLabel ) orElse
          andR( existingLabel ) orElse
          orL( existingLabel ) orElse
          orR( existingLabel ) orElse
          impL( existingLabel ) orElse
          impR( existingLabel ) orElse
          negL( existingLabel ) orElse
          negR( existingLabel )
        tac( goal )
      case None => None
    }
  }
}

/**
 * Chain
 */
case class ChainTactic( hyp: String, target: Option[String] = None ) extends Tactic {

  override def apply( goal: OpenAssumption ) = {
    val goalSequent = goal.s

    ???
  }

  def at( target: String ) = new ChainTactic( hyp, Option( target ) )
}

/**
 * Solves propositional sub goal
 */
case object PropTactic extends Tactic {
  override def apply( goal: OpenAssumption ) = {
    solve.solvePropositional( goal.conclusion ) match {
      case None      => None
      case Some( z ) => Option( z )
    }
  }
}

/**
 * Solves sub goal with Prover9
 */
case object Prover9Tactic extends Tactic {
  override def apply( goal: OpenAssumption ) = {
    Prover9.getLKProof( goal.conclusion ) match {
      case None      => None
      case Some( z ) => Option( z )
    }
  }
}

/**
 *
 */
case class ForgetTactic( applyToLabel: String ) extends Tactic {
  override def apply( goal: OpenAssumption ) = {
    val f = WeakeningLeftTactic( applyToLabel ) orElse WeakeningRightTactic( applyToLabel )
    f( goal )
  }
}
