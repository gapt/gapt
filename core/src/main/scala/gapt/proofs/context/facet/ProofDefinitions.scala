package gapt.proofs.context.facet

import gapt.expr.Expr
import gapt.expr.Substitution
import gapt.expr.syntacticMatching
import gapt.proofs.SequentConnector
import gapt.proofs.context.ProofDefinition
import gapt.proofs.lk.LKProof

case class ProofDefinitions( components: Map[String, Set[ProofDefinition]] ) {
  def +( defn: ProofDefinition ) =
    copy( components.updated(
      defn.proofName,
      components.getOrElse( defn.proofName, Set() ) + defn ) )

  def findWithConnector( name: Expr ): Iterable[( SequentConnector, Substitution, LKProof )] =
    for {
      defs <- components.values
      defn <- defs
      subst <- syntacticMatching( defn.proofNameTerm, name )
    } yield ( defn.connector, subst, defn.proof )

  def find( name: Expr ): Iterable[( LKProof, Substitution )] =
    for ( ( _, subst, proof ) <- findWithConnector( name ) ) yield ( proof, subst )
  override def toString: String =
    components.map { case ( n, dfs ) => dfs.map( _.proofNameTerm ).mkString( ", " ) }.mkString( "\n" )
}
object ProofDefinitions {
  implicit val ProofDefinitionsFacet: Facet[ProofDefinitions] = Facet( ProofDefinitions( Map() ) )
}
