package gapt.proofs.gaptic

import gapt.expr._
import gapt.formats.babel.BabelSignature
import gapt.proofs.{ HOLSequent, Sequent }
import gapt.proofs.context.Context
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.context.update.ProofDeclaration
import gapt.proofs.lk._
import gapt.proofs.lk.transformations.cleanStructuralRules
import gapt.utils.Maybe

case class CanLabelledSequent( labelledSequent: Sequent[( String, Formula )] ) extends AnyVal
object CanLabelledSequent {
  implicit def fromLabelledSequent( labelledSequent: Sequent[( String, Formula )] ): CanLabelledSequent =
    CanLabelledSequent( labelledSequent )
  implicit def fromSequent( sequent: HOLSequent ): CanLabelledSequent =
    guessLabels( sequent )
  implicit def fromFormula( formula: Formula ): CanLabelledSequent =
    Sequent() :+ formula
}

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
    ctx += ProofDeclaration( lhs, proof )
    proof
  }

  class Helper( labelledSequent: Sequent[( String, Formula )] ) extends LemmaHelper[LKProof] {
    def handleTacticBlock( proof: ProofState => ProofState )( implicit ctx: MutableContext, name: sourcecode.Name ): LKProof =
      finish( implicitly[sourcecode.Name].value, proof( ProofState( labelledSequent ) ), incompleteOk = false )
  }
  def apply[T]( labelledSequent: CanLabelledSequent ): Helper =
    new Helper( labelledSequent.labelledSequent )
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
  def apply[T]( labelledSequent: CanLabelledSequent ): Helper =
    new Helper( labelledSequent.labelledSequent )
}
object IncompleteProof {
  class Helper( labelledSequent: Sequent[( String, Formula )] ) extends LemmaHelper[LKProof] {
    def handleTacticBlock( proof: ProofState => ProofState )( implicit sig: BabelSignature, ctx: Maybe[Context] ): LKProof =
      Proof.finish( proof( ProofState( labelledSequent ) ), incompleteOk = true )
  }
  def apply[T]( labelledSequent: CanLabelledSequent ): Helper =
    new Helper( labelledSequent.labelledSequent )
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
