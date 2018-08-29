package gapt.proofs.context.update

import gapt.expr.Apps
import gapt.expr.Const
import gapt.expr.Expr
import gapt.proofs.SequentConnector
import gapt.proofs.context.Context
import gapt.proofs.context.Context.ProofDefinition
import gapt.proofs.context.Context.ProofDefinitions
import gapt.proofs.context.Context.ProofNames
import gapt.proofs.context.State
import gapt.proofs.lk.LKProof

case class ProofDefinitionDeclaration( lhs: Expr, referencedProof: LKProof ) extends Update {
  override def apply( ctx: Context ): State = {
    ctx.check( referencedProof )
    val Apps( c: Const, vs ) = lhs
    vs.foreach( ctx.check( _ ) )
    val declSeq = ctx.get[ProofNames].lookup( lhs )
      .getOrElse( throw new IllegalArgumentException( s"Proof name ${lhs.toSigRelativeString( ctx )} is not defined" ) )
    require(
      referencedProof.conclusion.isSubMultisetOf( declSeq ),
      "End-sequent of proof definition does not match declaration.\n" +
        "Given sequent: " + referencedProof.endSequent.toSigRelativeString( ctx ) + "\n" +
        "Expected sequent: " + declSeq.toSigRelativeString( ctx ) + "\n" +
        "Extraneous formulas: " +
        referencedProof.endSequent.diff( declSeq ).toSigRelativeString( ctx ) )
    val conn = SequentConnector.guessInjection( fromLower = referencedProof.conclusion, toUpper = declSeq )
    val defn = ProofDefinition( lhs, conn, referencedProof )
    ctx.state.update[ProofDefinitions]( _ + defn )
  }
}