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
      throw new TacticFailureException( "Failed to apply tactic " + tactical + " to proof state with sub goals:\n" + proofState.subGoals.map { _.toPrettyString }.mkString( "\n" ) )
    }

  def qed( proofState: ProofState ): LKProof =
    if ( proofState.subGoals.isEmpty ) {
      proofState.proofSegment
    } else {
      throw new QedFailureException( "Proof not completed. There are still " + proofState.subGoals.length + " unproved sub goals:\n" + proofState.subGoals.map { _.toPrettyString }.mkString( "\n" ) )
    }

  import reflect.macros._
  def applyImpl( c: blackbox.Context )( labelledSequent: c.Tree )( tacticsProof: c.Tree ): c.Tree = {
    import c.universe._
    val proofState = TermName( c.freshName() )

    val lemmaMacros = symbolOf[LemmaMacros.type].asClass.module
    val proofStateCompanion = symbolOf[ProofState.type].asClass.module
    val openAssumptionCompanion = symbolOf[OpenAssumption.type].asClass.module

    val tacticsStmts = tacticsProof match {
      case q"{..$stmts}" =>
        for ( stmt <- stmts )
          yield q"$proofState = $lemmaMacros.use($proofState, $stmt)"
    }

    q"""
      var $proofState = $proofStateCompanion(0, $openAssumptionCompanion($labelledSequent))

      ..$tacticsStmts

      $lemmaMacros.qed($proofState)
    """
  }
}

class TacticFailureException( s: String ) extends Throwable( s )

class QedFailureException( s: String ) extends Throwable( s )
