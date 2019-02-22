package gapt.expr.formula.prop

import gapt.expr.Const
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.fol.FOLAtomConst
import gapt.expr.ty.To

trait PropAtom extends Const with PropFormula with FOLAtom with FOLAtomConst

object PropAtom {
  def apply( sym: String ): PropAtom = Const( sym, To ).asInstanceOf[PropAtom]
}