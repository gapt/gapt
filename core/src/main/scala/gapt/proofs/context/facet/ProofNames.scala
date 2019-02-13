package gapt.proofs.context.facet

import gapt.expr.Expr
import gapt.expr.clauseSubsumption
import gapt.expr.syntacticMatching
import gapt.proofs.HOLSequent
import gapt.proofs.lk.rules.ProofLink

case class ProofNames( names: Map[String, ( Expr, HOLSequent )] ) {
  def +( name: String, referencedExpression: Expr, referencedSequent: HOLSequent ) = copy( names + ( ( name, ( referencedExpression, referencedSequent ) ) ) )

  def sequents: Iterable[HOLSequent] =
    for ( ( _, ( _, seq ) ) <- names ) yield seq

  def lookup( name: Expr ): Option[HOLSequent] =
    ( for {
      ( declName, declSeq ) <- names.values
      subst <- syntacticMatching( declName, name )
    } yield subst( declSeq ) ).headOption

  def link( name: Expr ): Option[ProofLink] =
    for ( sequent <- lookup( name ) ) yield ProofLink( name, sequent )

  def find( seq: HOLSequent ): Option[Expr] =
    ( for {
      ( declName, declSeq ) <- names.values
      subst <- clauseSubsumption( declSeq, seq, multisetSubsumption = true )
    } yield subst( declName ) ).headOption

  override def toString: String =
    names.toSeq.sortBy( _._1 ).
      map { case ( _, ( lhs, sequent ) ) => s"$lhs: $sequent" }.
      mkString( "\n" )
}

object ProofNames {
  implicit val ProofsFacet: Facet[ProofNames] = Facet( ProofNames( Map[String, ( Expr, HOLSequent )]() ) )
}