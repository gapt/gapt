package gapt.provers.viper.grammars

import gapt.expr._
import gapt.expr.hol.containsStrongQuantifier
import gapt.proofs.expansion.ExpansionProof
import gapt.proofs.{ Context, HOLSequent, MutableContext, Sequent, Suc }
import gapt.proofs.lk.{ LKProof, LKToExpansionProof, instanceProof, skolemizeLK }
import gapt.proofs.lkt.{ LKToLKt, LKt, LKtToLK, LocalCtx, atomizeEquality, normalizeLKt }
import gapt.provers.OneShotProver
import gapt.utils.Maybe

case class IndElimProver(
    proofTerm: LKt,
    lctx:      LocalCtx,
    ctx:       Context ) extends OneShotProver {
  val instSeq = lctx.toSequent
  val goal = instSeq.succedent.head
  val xs = freeVariables( goal ).toSeq
  val quantSequent = instSeq.copy( succedent = Vector( All.Block( xs, goal ) ) )

  def apply( ts: Seq[Expr] ): LKt =
    normalizeLKt.induction( Substitution( xs zip ts )( proofTerm ), lctx )( ctx )

  def getLKtProof( seq: HOLSequent ): LKt = {
    val Some( subst ) = syntacticMatching( goal, seq( Suc( 0 ) ) )
    require( subst( instSeq ) isSubsetOf seq )
    apply( subst( xs ) )
  }

  override def getExpansionProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[ExpansionProof] =
    getLKProof( seq ).map( LKToExpansionProof( _ ) )
  override def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] =
    Some( LKtToLK( getLKtProof( seq ), lctx ) )
}

object IndElimProver {
  def apply(
    proof: LKProof )( implicit ctx: Context ): IndElimProver = {
    implicit val mctx = ctx.newMutable
    val Sequent( _, Seq( All.Block( xs, goal ) ) ) = proof.endSequent
    val proof1 = instanceProof( proof, xs )
    val proof2 =
      if ( !containsStrongQuantifier( proof1.endSequent ) ) proof1
      else skolemizeLK( proof1, proofTheoretic = false )
    val ( proofTerm0, lctx ) = LKToLKt( proof2 )
    val proofTerm1 = atomizeEquality( proofTerm0, lctx )
    val proofTerm2 = normalizeLKt( proofTerm1 )
    IndElimProver( proofTerm2, lctx, mctx.toImmutable )
  }
}

object indElimReversal {
  def apply( proof: LKProof, opts: TreeGrammarProverOptions )( implicit ctx0: Context ): LKProof =
    apply( IndElimProver( proof ), opts )

  def apply( instProver: IndElimProver, opts: TreeGrammarProverOptions ): LKProof = {
    val prover = new TreeGrammarProver( instProver.ctx, instProver.quantSequent,
      opts.copy( instanceProver = instProver ) )
    prover.solve()
  }
}
