package gapt.expr.formula.hol

import gapt.expr.App
import gapt.expr.Expr
import gapt.expr.formula.Atom

trait HOLPartialAtom extends Expr {
  private[expr] def numberOfArguments: Int

  def apply( that: Expr* )( implicit dummyImplicit: DummyImplicit ) = App( this, that ).asInstanceOf[Atom]
}
