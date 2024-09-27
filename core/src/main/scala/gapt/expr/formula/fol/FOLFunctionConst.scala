package gapt.expr.formula.fol

import gapt.expr.App
import gapt.expr.Const
import gapt.expr.ty.Ti

trait FOLFunctionConst extends Const with FOLPartialTerm {
  def apply(that: FOLTerm*)(implicit dummyImplicit: DummyImplicit): FOLTerm = App(this, that).asInstanceOf[FOLTerm]
}

object FOLFunctionConst extends FOLHead(Ti) {
  override def apply(sym: String, arity: Int): FOLFunctionConst =
    super.apply(sym, arity).asInstanceOf[FOLFunctionConst]
}
