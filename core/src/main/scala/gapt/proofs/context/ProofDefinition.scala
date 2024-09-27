package gapt.proofs.context

import gapt.expr.Apps
import gapt.expr.Const
import gapt.expr.Expr
import gapt.proofs.SequentConnector
import gapt.proofs.lk.LKProof

case class ProofDefinition(proofNameTerm: Expr, connector: SequentConnector, proof: LKProof) {
  val Apps(Const(proofName, _, _), _) = proofNameTerm: @unchecked
}
