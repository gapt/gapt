package gapt.proofs.lk.rules.macros

import gapt.expr.All
import gapt.expr.Ex
import gapt.expr.Expr
import gapt.expr.Formula
import gapt.proofs.lk.LKProof

object WeakQuantifierBlock {
  def apply( p: LKProof, main: Formula, terms: Seq[Expr] ) =
    main match {
      case _ if terms.isEmpty => p
      case All( _, _ )        => ForallLeftBlock( p, main, terms )
      case Ex( _, _ )         => ExistsRightBlock( p, main, terms )
    }
}
