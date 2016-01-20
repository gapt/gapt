package at.logic.gapt.proofs.gaptic

import at.logic.gapt.expr.HOLFormula
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.lk._

import language.experimental.macros

object Lemma {
  def apply( labelledSequent: Sequent[( String, HOLFormula )] )( tacticsProof: => Tactical ): LKProof = macro LemmaMacros.applyImpl
}

object LemmaMacros {

  def use( proofState: ProofState, tactical: Tactical ): ProofState =
    tactical( proofState ) getOrElse {
      throw new TacticFailureException( "Failed to apply tactic " + tactical + " to proof state " + proofState )
    }

  def qed( proofState: ProofState ): LKProof =
    if ( proofState.subGoals.isEmpty ) {
      proofState.proofSegment
    } else {
      throw new QedFailureException( "Proof not completed. There are still " + proofState.subGoals.length + " unproved sub goals:\n" + proofState.subGoals.mkString( "\n" ) )
    }

  import reflect.macros._
  def applyImpl( c: blackbox.Context )( labelledSequent: c.Tree )( tacticsProof: c.Tree ): c.Tree = {
    import c.universe._
    val proofState = TermName( c.freshName() )

    val tacticsStmts = tacticsProof match {
      case q"{..$stmts}" =>
        for ( stmt <- stmts )
          yield q"$proofState = _root_.at.logic.gapt.proofs.gaptic.LemmaMacros.use($proofState, $stmt)"
    }

    q"""
      var $proofState = _root_.at.logic.gapt.proofs.gaptic.ProofState(0,
        _root_.at.logic.gapt.proofs.gaptic.OpenAssumption($labelledSequent))

      ..$tacticsStmts

      _root_.at.logic.gapt.proofs.gaptic.LemmaMacros.qed($proofState)
    """
  }
}

class TacticFailureException( s: String ) extends Throwable( s )

class QedFailureException( s: String ) extends Throwable( s )
