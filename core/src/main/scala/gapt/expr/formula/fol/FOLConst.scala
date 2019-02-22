package gapt.expr.formula.fol

import gapt.expr.Const

trait FOLConst extends Const with FOLTerm with FOLFunctionConst

object FOLConst {
  def apply( sym: String ): FOLConst = FOLFunction( sym ).asInstanceOf[FOLConst]
  def unapply( e: FOLConst ) = Some( e.name )
}