package gapt.proofs.context.facet

import gapt.expr.ty.TBase
import gapt.expr.ty.TVar

/** Base types, including inductive types. */
case class BaseTypes(baseTypes: Map[String, TBase]) {
  def +(ty: TBase): BaseTypes = {
    require(ty.params.forall(_.isInstanceOf[TVar]) && ty.params == ty.params.distinct)
    require(
      !baseTypes.contains(ty.name),
      s"Base type $ty already defined."
    )
    copy(baseTypes + (ty.name -> ty))
  }
  override def toString = baseTypes.toSeq.sortBy(_._1).map(_._2).mkString(", ")
}

object BaseTypes {
  implicit val baseTypesFacet: Facet[BaseTypes] = Facet(BaseTypes(Map()))
}
