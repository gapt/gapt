package gapt.proofs.context.facet

import gapt.expr.Const

/** Inductive types, for each type we store its list of constructors. */
case class StructurallyInductiveTypes( constructors: Map[String, Vector[Const]] ) {
  def +( ty: String, ctrs: Vector[Const] ) =
    copy( constructors + ( ty -> ctrs ) )

  override def toString: String = constructors.toSeq.sortBy( _._1 ).
    map { case ( t, cs ) => s"$t: ${cs.mkString( ", " )}" }.mkString( "\n" )
}
object StructurallyInductiveTypes {
  implicit val structIndTysFacet: Facet[StructurallyInductiveTypes] = Facet( StructurallyInductiveTypes( Map() ) )
}
