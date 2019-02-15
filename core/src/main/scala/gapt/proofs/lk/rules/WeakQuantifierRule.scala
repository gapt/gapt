package gapt.proofs.lk.rules

import gapt.expr.Expr
import gapt.expr.Var
import gapt.expr.formula.Formula
import gapt.proofs.SequentIndex
import gapt.proofs.lk.LKProof

object WeakQuantifierRule {
  def unapply( p: UnaryLKProof ): Option[( LKProof, SequentIndex, Formula, Expr, Var, Boolean )] = p match {
    case ForallLeftRule( subProof, aux, f, t, v ) =>
      Some( ( subProof, aux, f, t, v, false ) )
    case ExistsRightRule( subProof, aux, f, t, v ) =>
      Some( ( subProof, aux, f, t, v, true ) )
    case _ => None
  }
}
