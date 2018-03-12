package gapt.proofs.gaptic

import gapt.expr._
import gapt.formats.babel.BabelSignature
import gapt.proofs.{ Context, MutableContext, Sequent }
import gapt.proofs.lk._
import gapt.utils.Maybe

object Lemma {
  def finish( proofState: ProofState, incompleteOk: Boolean )( implicit sig: BabelSignature ): LKProof =
    if ( incompleteOk ) {
      cleanStructuralRules( proofState.partialProof )
    } else if ( proofState.subGoals.isEmpty ) {
      cleanStructuralRules( proofState.result )
    } else {
      throw new QedFailureException(
        s"Proof not completed. There are still ${proofState.subGoals.length} open sub goals:\n" +
          proofState.subGoals.map { _.toPrettyString }.mkString( "\n" ) )
    }

  def finish( lemmaName: String, proofState: ProofState, incompleteOk: Boolean )( implicit ctx: MutableContext ): LKProof =
    addToCtx( lemmaName, finish( proofState, incompleteOk ) )

  def addToCtx( lemmaName: String, proof: LKProof )( implicit ctx: MutableContext ): LKProof = {
    val fvs = freeVariables( proof.endSequent ).toSeq.sortBy( _.name )
    val ftvs = typeVariables( proof.endSequent.toImplication ).toList.sortBy( _.name )
    val lhs = Const( lemmaName, FunctionType( Ti, fvs.map( _.ty ) ), ftvs )( fvs )
    ctx += Context.ProofDeclaration( lhs, proof )
    proof
  }

  class Helper( labelledSequent: Sequent[( String, Formula )] ) extends LemmaHelper[LKProof] {
    def handleTacticBlock( proof: ProofState => ProofState )( implicit ctx: MutableContext, name: sourcecode.Name ): LKProof =
      finish( implicitly[sourcecode.Name].value, proof( ProofState( labelledSequent ) ), incompleteOk = false )
  }
  def apply[T]( labelledSequent: Sequent[( String, Formula )] ): Helper =
    new Helper( labelledSequent )
  def apply[T]( formula: Formula ): Helper =
    apply( guessLabels( Sequent() :+ formula ) )
}

object Proof {
  def finish( proofState: ProofState, incompleteOk: Boolean )( implicit sig: BabelSignature, ctx: Maybe[Context] ): LKProof = {
    val p = Lemma.finish( proofState, incompleteOk )
    if ( !incompleteOk ) ctx.foreach( _.check( p ) )
    p
  }
  class Helper( labelledSequent: Sequent[( String, Formula )] ) extends LemmaHelper[LKProof] {
    def handleTacticBlock( proof: ProofState => ProofState )( implicit sig: BabelSignature, ctx: Maybe[Context] ): LKProof =
      finish( proof( ProofState( labelledSequent ) ), incompleteOk = false )
  }
  def apply[T]( labelledSequent: Sequent[( String, Formula )] ): Helper =
    new Helper( labelledSequent )
  def apply[T]( formula: Formula ): Helper =
    apply( guessLabels( Sequent() :+ formula ) )
}
object IncompleteProof {
  class Helper( labelledSequent: Sequent[( String, Formula )] ) extends LemmaHelper[LKProof] {
    def handleTacticBlock( proof: ProofState => ProofState )( implicit sig: BabelSignature, ctx: Maybe[Context] ): LKProof =
      Proof.finish( proof( ProofState( labelledSequent ) ), incompleteOk = true )
  }
  def apply[T]( labelledSequent: Sequent[( String, Formula )] ): Helper =
    new Helper( labelledSequent )
}

class TacticFailureException( s: String, cause: Throwable = null ) extends Exception( s, cause )
case class TacticFailureFailureException( error: TacticFailure )( implicit sig: BabelSignature )
  extends TacticFailureException( error.toSigRelativeString )

class QedFailureException( s: String ) extends Exception( s )

trait SimpleLemmaHelper[T] extends LemmaHelper[T] {
  def handleTacticBlock( block: ProofState => ProofState ): T
}
trait TacticBlockArgument[T] extends SimpleLemmaHelper[T] {
  def handleTactic( block: Tactic[Unit] ): T

  def handleTacticBlock( block: ProofState => ProofState ): T =
    handleTactic( proofState =>
      try Right( () -> block( proofState ) ) catch {
        case TacticFailureFailureException( error ) => Left( error )
      } )
}
