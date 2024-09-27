package gapt.proofs.context.update

import gapt.expr.Expr
import gapt.proofs.context.Context
import gapt.proofs.context.State
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.ProofLink

case class ProofDeclaration(lhs: Expr, proof: LKProof) extends Update {
  def link = ProofLink(lhs, proof.endSequent)

  override def apply(ctx: Context): State =
    ctx + ProofNameDeclaration(lhs, proof.endSequent) + ProofDefinitionDeclaration(lhs, proof) state

  override def toString: String =
    s"ProofDeclaration($lhs, ${proof.endSequent})"
}
