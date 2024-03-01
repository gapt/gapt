package gapt.provers.viper.grammars

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.hol.containsStrongQuantifier
import gapt.expr.subst.Substitution
import gapt.expr.util.freeVariables
import gapt.expr.util.syntacticMatching
import gapt.proofs.context.Context
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.expansion.ExpansionProof
import gapt.proofs.lk.transformations.LKToExpansionProof
import gapt.proofs.lk.transformations.skolemizeLK
import gapt.proofs.lk.util.instanceProof
import gapt.proofs.{ HOLSequent, Sequent, Suc }
import gapt.proofs.lk.{ LKProof, normalizeLKt }
import gapt.proofs.lkt.{ LKToLKt, LKt, LKtToLK, LocalCtx, closedUnderSubstitution }
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

  def apply( ts: Seq[Expr] ): ( LKt, LocalCtx ) = {
    val subst = Substitution( xs zip ts )
    val lctx1 = subst( lctx )
    normalizeLKt.induction( subst( proofTerm ), lctx1 )( ctx ) -> lctx1
  }

  def getLKtProof( seq: HOLSequent ): ( LKt, LocalCtx ) = {
    val Some( subst ) = syntacticMatching( goal, seq( Suc( 0 ) ) ): @unchecked
    require( subst( instSeq ) isSubsetOf seq )
    apply( subst( xs ) )
  }

  override def getExpansionProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[ExpansionProof] =
    getLKProof( seq ).map( LKToExpansionProof( _ ) )
  override def getLKProof( seq: HOLSequent )( implicit ctx: Maybe[MutableContext] ): Option[LKProof] = {
    val ( q, lctx1 ) = getLKtProof( seq )
    Some( LKtToLK.apply( q, lctx1 ) )
  }
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
    val proofTerm1 = normalizeLKt.induction( proofTerm0, lctx )
    IndElimProver( proofTerm1, lctx, mctx.toImmutable )
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
