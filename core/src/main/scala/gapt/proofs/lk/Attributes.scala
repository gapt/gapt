package gapt.proofs.lk

import gapt.proofs.context.Context
import gapt.proofs.context.facet.ProofNames
import gapt.proofs.context.State
import gapt.proofs.context.facet.Facet
import gapt.proofs.context.update.Update

case class Attributes( attrs: Map[String, Set[String]] ) {
  def +( lemmaName: String, attrName: String ): Attributes = copy( attrs =
    attrs.updated( lemmaName, attrs( lemmaName ) + attrName ) )

  def has( lem: String, attr: String ): Boolean =
    attrs( lem ).contains( attr )

  def lemmasWith( attr: String ): Set[String] =
    ( for ( ( n, as ) <- attrs.view if as( attr ) ) yield n ).toSet

  override def toString: String = {
    for ( ( l, as ) <- attrs.toSeq.sortBy( _._1 ) )
      yield s"$l: ${as.mkString( ", " )}"
  }.mkString( "\n" )
}

object Attributes {
  implicit val facet: Facet[Attributes] = Facet( Attributes( Map().withDefaultValue( Set() ) ) )

  case class AddAttributeUpdate( lemmaName: String, attrName: String ) extends Update {
    override def apply( ctx: Context ): State = {
      require( ctx.get[ProofNames].names.contains( lemmaName ), s"unknown lemma: $lemmaName" )
      ctx.state.update[Attributes]( _.+( lemmaName, attrName ) )
    }
  }
}