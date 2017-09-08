package at.logic.gapt.proofs.gaptic

import at.logic.gapt.expr._
import at.logic.gapt.formats.babel.BabelSignature
import at.logic.gapt.proofs.{ Context, MutableContext, Sequent }
import at.logic.gapt.proofs.lk._
import at.logic.gapt.utils.Maybe

import language.experimental.macros

object Lemma {
  def apply[T]( labelledSequent: Sequent[( String, Formula )] )( tacticsProof: => Tactical[T] ): LKProof = macro LemmaMacros.lemmaImpl
}

object Proof {
  def apply[T]( labelledSequent: Sequent[( String, Formula )] )( tacticsProof: => Tactical[T] ): LKProof = macro LemmaMacros.proofImpl
}
object IncompleteProof {
  def apply[T]( labelledSequent: Sequent[( String, Formula )] )( tacticsProof: => Tactical[T] ): LKProof = macro LemmaMacros.incompleteProofImpl
}

object LemmaMacros {

  def use[T]( proofState: ProofState, tactical: Tactical[T] )( implicit sig: BabelSignature ): ProofState =
    ( try tactical( proofState ) catch {
      case t: Throwable =>
        throw new TacticFailureException(
          s"Exception when applying $tactical to proof state with sub goals:\n" +
            proofState.subGoals.map { _.toPrettyString }.mkString( "\n" ),
          t )
    } ) match {
      case Right( ( _, newState ) ) => newState
      case Left( error ) =>
        throw new TacticFailureException( error.toSigRelativeString )
    }

  private def finish( proofState: ProofState, incompleteOk: Boolean )( implicit sig: BabelSignature ): LKProof =
    if ( incompleteOk ) {
      cleanStructuralRules( proofState.partialProof )
    } else if ( proofState.subGoals.isEmpty ) {
      cleanStructuralRules( proofState.result )
    } else {
      throw new QedFailureException(
        s"Proof not completed. There are still ${proofState.subGoals.length} open sub goals:\n" +
          proofState.subGoals.map { _.toPrettyString }.mkString( "\n" ) )
    }

  def finishProof( proofState: ProofState, incompleteOk: Boolean )( implicit sig: BabelSignature, ctx: Maybe[Context] ): LKProof = {
    val p = finish( proofState, incompleteOk )
    if ( !incompleteOk ) ctx.foreach( _.check( p ) )
    p
  }

  def finishLemma( lemmaName: String, proofState: ProofState, incompleteOk: Boolean )( implicit ctx: MutableContext ): LKProof = {
    val proof = finish( proofState, incompleteOk )
    val fvs = freeVariablesLK( proof ).toSeq.sortBy( _.name )
    val lhs = Const( lemmaName, FunctionType( Ti, fvs.map( _.ty ) ) )( fvs )
    ctx += Context.ProofDeclaration( lhs, proof )
    proof
  }

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

  def lemmaImpl( c: blackbox.Context )( labelledSequent: c.Tree )( tacticsProof: c.Tree ): c.Tree = {
    import c.universe._
    val construction = constructProofState( c )( labelledSequent, tacticsProof )
    val lemmaMacros = symbolOf[LemmaMacros.type].asClass.module

    val term = c.internal.enclosingOwner.asTerm
    val name = term.name.decodedName.toString

    q"$lemmaMacros.finishLemma($name, $construction, incompleteOk = false)"
  }

  def proofImpl( c: blackbox.Context )( labelledSequent: c.Tree )( tacticsProof: c.Tree ): c.Tree = {
    import c.universe._
    val construction = constructProofState( c )( labelledSequent, tacticsProof )
    val lemmaMacros = symbolOf[LemmaMacros.type].asClass.module

    q"$lemmaMacros.finishProof($construction, incompleteOk = false)"
  }

  def incompleteProofImpl( c: blackbox.Context )( labelledSequent: c.Tree )( tacticsProof: c.Tree ): c.Tree = {
    import c.universe._
    val construction = constructProofState( c )( labelledSequent, tacticsProof )
    val lemmaMacros = symbolOf[LemmaMacros.type].asClass.module

    q"$lemmaMacros.finishProof($construction, incompleteOk = true)"
  }
}

class TacticFailureException( s: String, cause: Throwable = null ) extends Throwable( s, cause )

class QedFailureException( s: String ) extends Throwable( s )
