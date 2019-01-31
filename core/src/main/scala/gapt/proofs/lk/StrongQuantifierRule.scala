package gapt.proofs.lk

import gapt.expr.Var
import gapt.proofs.SequentIndex

object StrongQuantifierRule {
  def unapply( p: UnaryLKProof ): Option[( LKProof, SequentIndex, Var, Var, Boolean )] = p match {
    case ExistsLeftRule( subProof, aux, eigen, quant ) =>
      Some( ( subProof, aux, eigen, quant, false ) )
    case ForallRightRule( subProof, aux, eigen, quant ) =>
      Some( ( subProof, aux, eigen, quant, true ) )
    case _ => None
  }
}
