package at.logic.gapt.proofs.gaptic.tactics

import at.logic.gapt.expr._
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.gaptic.{ OpenAssumption, ProofState, Tactic, Tactical }
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
 * Solves propositional sub goals
 */
case object PropTactic extends Tactical {
  override def apply( proofState: ProofState ) = {

    def f( x: ProofState, i: Int ): ProofState = {
      x getSubGoal i match {
        case None => x
        case Some( y ) =>
          solve.solvePropositional( y.conclusion ) match {
            case None      => f( x, i + 1 )
            case Some( z ) => f( x replaceSubGoal ( i, z ), 0 )
          }
      }
    }

    Option( f( proofState, 0 ) )
  }
}

/**
 * Solves sub goals solvable by Prover9
 */
case object Prover9Tactic extends Tactical {
  override def apply( proofState: ProofState ) = {

    def f( x: ProofState, i: Int ): ProofState = {
      x getSubGoal i match {
        case None => x
        case Some( y ) =>
          Prover9.getLKProof( y.conclusion ) match {
            case None      => f( x, i + 1 )
            case Some( z ) => f( x replaceSubGoal ( i, z ), 0 )
          }
      }
    }

    Option( f( proofState, 0 ) )
  }
}