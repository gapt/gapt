package gapt.proofs.lk.rules.macros

import gapt.expr.Expr
import gapt.expr.formula.All
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.proofs.lk.LKProof

object WeakQuantifierBlock {
  def apply( p: LKProof, main: Formula, terms: Seq[Expr] ): LKProof =
    main match {
      case _ if terms.isEmpty => p
      case All( _, _ )        => ForallLeftBlock( p, main, terms )
      case Ex( _, _ )         => ExistsRightBlock( p, main, terms )
    }
}
