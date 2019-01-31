package gapt.proofs.lk

import gapt.expr.Expr
import gapt.expr.Formula
import gapt.expr.Var
import gapt.proofs.SequentIndex

object WeakQuantifierRule {
  def unapply( p: UnaryLKProof ): Option[( LKProof, SequentIndex, Formula, Expr, Var, Boolean )] = p match {
    case ForallLeftRule( subProof, aux, f, t, v ) =>
      Some( ( subProof, aux, f, t, v, false ) )
    case ExistsRightRule( subProof, aux, f, t, v ) =>
      Some( ( subProof, aux, f, t, v, true ) )
    case _ => None
  }
}
