package gapt.expr.formula.fol

import gapt.expr.Var
import gapt.expr.ty.Ti

trait FOLVar extends Var with FOLTerm

object FOLVar {
  def apply( sym: String ): FOLVar = Var( sym, Ti ).asInstanceOf[FOLVar]
  def unapply( e: FOLVar ) = Some( e.name )
}