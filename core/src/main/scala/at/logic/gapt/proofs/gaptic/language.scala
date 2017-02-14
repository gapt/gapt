package at.logic.gapt.proofs.gaptic

import at.logic.gapt.expr.HOLFormula
import at.logic.gapt.formats.babel.BabelSignature
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.lk._

import language.experimental.macros

object Lemma {
  def apply[T]( labelledSequent: Sequent[( String, HOLFormula )] )( tacticsProof: => Tactical[T] ): LKProof = macro LemmaMacros.applyImpl
}

object IncompleteLemma {
  def apply[T]( labelledSequent: Sequent[( String, HOLFormula )] )( tacticsProof: => Tactical[T] ): LKProof = macro LemmaMacros.incompleteImpl
}

object LemmaMacros {

  def use[T]( proofState: ProofState, tactical: Tactical[T] )( implicit sig: BabelSignature ): ProofState =
    ( try tactical( proofState ) catch {
      case t: Throwable =>
        throw new TacticFailureException(
          s"Exception when applying $tactical to proof state with sub goals:\n" +
            proofState.subGoals.map { _.toPrettyString }.mkString( "\n" ),
          t
        )
    } ) match {
      case Right( ( _, newState ) ) => newState
      case Left( error ) =>
        throw new TacticFailureException( error.toSigRelativeString )
    }

  def finishProof( proofState: ProofState )( implicit sig: BabelSignature ): LKProof =
    if ( proofState.subGoals.isEmpty ) {
      cleanStructuralRules( proofState.result )
    } else {
      throw new QedFailureException(
        s"Proof not completed. There are still ${proofState.subGoals.length} open sub goals:\n" +
          proofState.subGoals.map { _.toPrettyString }.mkString( "\n" )
      )
    }

  def finishIncompleteProof( proofState: ProofState )( implicit sig: BabelSignature ): LKProof =
    cleanStructuralRules( proofState.partialProof )

  import reflect.macros._
  def constructProofState( c: blackbox.Context )( labelledSequent: c.Tree, tacticsProof: c.Tree ): c.Tree = {
    import c.universe._
    val proofState = TermName( c.freshName( "proofState" ) )

    val lemmaMacros = symbolOf[LemmaMacros.type].asClass.module
    val proofStateCompanion = symbolOf[ProofState.type].asClass.module

    val tacticsStmts = tacticsProof match {
      case q"{..$stmts}" =>
        for ( stmt <- stmts )
          yield atPos( stmt.pos )( q"$proofState = $lemmaMacros.use($proofState, $stmt)" )

    }

    q"""
      var $proofState = $proofStateCompanion($labelledSequent)

      ..$tacticsStmts

      $proofState
    """
  }

  def applyImpl( c: blackbox.Context )( labelledSequent: c.Tree )( tacticsProof: c.Tree ): c.Tree = {
    import c.universe._
    val construction = constructProofState( c )( labelledSequent, tacticsProof )
    val lemmaMacros = symbolOf[LemmaMacros.type].asClass.module

    q"$lemmaMacros.finishProof($construction)"
  }

  def incompleteImpl( c: blackbox.Context )( labelledSequent: c.Tree )( tacticsProof: c.Tree ): c.Tree = {
    import c.universe._
    val construction = constructProofState( c )( labelledSequent, tacticsProof )
    val lemmaMacros = symbolOf[LemmaMacros.type].asClass.module

    q"$lemmaMacros.finishIncompleteProof($construction)"
  }
}

class TacticFailureException( s: String, cause: Throwable = null ) extends Throwable( s, cause )

class QedFailureException( s: String ) extends Throwable( s )
