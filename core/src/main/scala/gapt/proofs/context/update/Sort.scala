package gapt.proofs.context.update

import gapt.expr.ty.TBase
import gapt.proofs.context.Context
import gapt.proofs.context.facet.BaseTypes
import gapt.proofs.context.State

/** Uninterpreted base type. */
case class Sort(ty: TBase) extends TypeDefinition {
  override def apply(ctx: Context): State =
    ctx.state.update[BaseTypes](_ + ty)
}

object Sort {
  def apply(tyName: String): Sort = Sort(TBase(tyName))
}
