package gapt.proofs.context.facet

import gapt.expr.Normalizer
import gapt.expr.ReductionRule

/** Definitional reductions. */
case class Reductions( normalizer: Normalizer ) {
  def ++( rules: Vector[ReductionRule] ): Reductions =
    copy( Normalizer( normalizer.rules ++ rules ) )

  def +( reductionRule: ReductionRule ): Reductions =
    copy( normalizer + reductionRule )

  override def toString: String =
    normalizer.rules.map { case ReductionRule( lhs, rhs ) => s"$lhs -> $rhs" }.mkString( "\n" )
}

object Reductions {
  implicit val reductionsFacet: Facet[Reductions] = Facet( Reductions( Normalizer( Set() ) ) )
}
