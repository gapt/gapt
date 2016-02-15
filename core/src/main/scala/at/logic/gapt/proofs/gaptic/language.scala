package at.logic.gapt.proofs.gaptic

import at.logic.gapt.expr.HOLFormula
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.lk._

import language.experimental.macros
import scalaz._
import Scalaz._

object Lemma {
  def apply[T]( labelledSequent: Sequent[( String, HOLFormula )] )( tacticsProof: => Tactical[T] ): LKProof = macro LemmaMacros.applyImpl
}

object LemmaMacros {

  def use[T]( proofState: ProofState, tactical: Tactical[T] ): ProofState =
    ( try tactical( proofState ) catch {
      case t: Throwable =>
        throw new TacticFailureException(
          s"Exception when applying $tactical to proof state with sub goals:\n" +
            proofState.subGoals.map { _.toPrettyString }.mkString( "\n" ) + "\n",
          t
        )
    } ) match {
      case Success( ( _, newState ) ) => newState
      case Failure( errors ) =>
        throw new TacticFailureException( "Failed to apply tactic " + tactical + " to proof state with sub goals:\n" + proofState.subGoals.map { _.toPrettyString }.mkString( "\n" ) + "\n" + errors.toList.mkString( "\n" ) )
    }

  def qed( proofState: ProofState ): LKProof =
    if ( proofState.subGoals.isEmpty ) {
      cleanStructuralRules( proofState.proofSegment )
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
          yield atPos( stmt.pos )( q"$proofState = $lemmaMacros.use($proofState, $stmt)" )

    }

    q"""
      var $proofState = $proofStateCompanion(0, $openAssumptionCompanion($labelledSequent))

      ..$tacticsStmts

      $lemmaMacros.qed($proofState)
    """
  }
}

class TacticFailureException( s: String, cause: Throwable = null ) extends Throwable( s, cause )

class QedFailureException( s: String ) extends Throwable( s )
