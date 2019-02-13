package gapt.proofs.lk.rules

import gapt.expr.Expr
import gapt.expr.Formula
import gapt.proofs.HOLSequent
import gapt.proofs.Sequent
import gapt.proofs.context.Context
import gapt.proofs.context.facet.ProofNames

case class ProofLink( referencedProof: Expr, referencedSequent: Sequent[Formula] ) extends InitialSequent {
  override def name: String = "link"
  override def conclusion: HOLSequent = referencedSequent
}

object ProofLink {
  def apply( referencedProof: Expr )( implicit ctx: Context ): ProofLink =
    ProofLink( referencedProof, ctx.get[ProofNames].lookup( referencedProof ).get )
  def apply( name: String )( implicit ctx: Context ): ProofLink =
    ProofLink( ctx.get[ProofNames].names( name )._1 )
}