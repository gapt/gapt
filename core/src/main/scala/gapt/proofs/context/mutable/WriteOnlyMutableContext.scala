package gapt.proofs.context.mutable

import gapt.expr.Const
import gapt.expr.Expr
import gapt.proofs.context.ImmutableContext

trait WriteOnlyMutableContext {

  def ctx_=( newContext: ImmutableContext ): Unit

  def addDefinition( by: Expr, name: => String, reuse: Boolean ): Const

  def addSkolemSym( defn: Expr, name: => String, reuse: Boolean ): Const

}
