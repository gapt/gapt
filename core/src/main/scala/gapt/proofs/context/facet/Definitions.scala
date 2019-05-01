package gapt.proofs.context.facet

import gapt.expr.Expr
import gapt.proofs.context.update.Definition

/** Definitions that define a constant by an expression of the same type. */
case class Definitions( definitions: Map[String, Expr] ) {
  def +( defn: Definition ) = {
    require( !definitions.contains( defn.what.name ) )
    copy( definitions + ( defn.what.name -> defn.by ) )
  }

  override def toString = definitions.toSeq.sortBy( _._1 ).
    map { case ( w, b ) => s"$w -> $b" }.mkString( "\n" )

  def filter( p: ( ( String, Expr ) ) => Boolean ): Definitions =
    copy( definitions.filter( p ) )
}
object Definitions {
  implicit val defsFacet: Facet[Definitions] = Facet( Definitions( Map() ) )
}

