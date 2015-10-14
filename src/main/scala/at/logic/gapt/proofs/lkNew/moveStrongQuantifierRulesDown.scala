package at.logic.gapt.proofs.lkNew

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.instantiate
import at.logic.gapt.proofs.{ OccConnector, Ant, Suc, Sequent }

/**
 * Modifies an LK proof to introduce strong quantifiers as soon as possible.
 */
object moveStrongQuantifierRulesDown {
  def apply( p: LKProof ): LKProof = apply( p, p.conclusion map { _ => Seq() } )._1

  private def apply( p: LKProof, eigenVariables: Sequent[Seq[Var]] ): ( LKProof, OccConnector[HOLFormula] ) = p.conclusion.zipWithIndex.elements.view.collect {
    case ( All.Block( vs, f ), i @ Suc( _ ) ) if vs.size > eigenVariables( i ).size =>
      val v = vs( eigenVariables( i ).size )
      val eigen = rename( v, freeVariablesLK( p ).toList ++ eigenVariables.elements.flatten )
      val ( q, oc ) = apply( p, eigenVariables.updated( i, eigenVariables( i ) :+ eigen ) )
      val q_ = ForallRightRule( q, oc.children( i ).head, eigen, v )
      ( q_, q_.getOccConnector * oc )
    case ( Ex.Block( vs, f ), i @ Ant( _ ) ) if vs.size > eigenVariables( i ).size =>
      val v = vs( eigenVariables( i ).size )
      val eigen = rename( v, freeVariablesLK( p ).toList ++ eigenVariables.elements.flatten )
      val ( q, oc ) = apply( p, eigenVariables.updated( i, eigenVariables( i ) :+ eigen ) )
      val q_ = ExistsLeftRule( q, oc.children( i ).head, eigen, v )
      ( q_, q_.getOccConnector * oc )
  }.headOption getOrElse {
    p match {
      case StrongQuantifierRule( subProof, aux, eigen, quant, isSuc ) =>
        val newEigen = eigenVariables( p.mainIndices.head ).head
        val ( q, oc ) = apply(
          applySubstitution( Substitution( eigen -> newEigen ) )( subProof ),
          p.occConnectors( 0 ).parents( eigenVariables ).map( _.head ).
            updated( aux, eigenVariables( p.mainIndices.head ).tail )
        )
        ( q, oc * p.occConnectors( 0 ).inv )

      case LogicalAxiom( atom )     => ( p, OccConnector( p.endSequent ) )
      case ReflexivityAxiom( term ) => ( p, OccConnector( p.endSequent ) )
      case TheoryAxiom( sequent )   => ( p, OccConnector( p.endSequent ) )

      case p @ WeakeningLeftRule( subProof, formula ) =>
        val ( q1, oc ) = apply( subProof, p.occConnectors( 0 ).parents( eigenVariables ).map( _.head ) )
        val q = WeakeningLeftRule( q1, instantiate( formula, eigenVariables( p.mainIndices.head ) ) )
        ( q, q.getOccConnector * oc * p.getOccConnector.inv + ( q.mainIndices.head, p.mainIndices.head ) )
      case p @ WeakeningRightRule( subProof, formula ) =>
        val ( q1, oc ) = apply( subProof, p.occConnectors( 0 ).parents( eigenVariables ).map( _.head ) )
        val q = WeakeningRightRule( q1, instantiate( formula, eigenVariables( p.mainIndices.head ) ) )
        ( q, q.getOccConnector * oc * p.getOccConnector.inv + ( q.mainIndices.head, p.mainIndices.head ) )

      case _ =>
        val ( qs, oc ) = ( for ( ( subProof, occConn ) <- p.immediateSubProofs zip p.occConnectors )
          yield apply( subProof, occConn.parents( eigenVariables ).map( _.headOption getOrElse Seq() ) ) ).unzip
        val q = p match {
          case ContractionLeftRule( _, aux1, aux2 )        => ContractionLeftRule( qs( 0 ), oc( 0 ).children( aux1 ).head, oc( 0 ).children( aux2 ).head )
          case ContractionRightRule( _, aux1, aux2 )       => ContractionRightRule( qs( 0 ), oc( 0 ).children( aux1 ).head, oc( 0 ).children( aux2 ).head )

          case CutRule( _, aux1, _, aux2 )                 => CutRule( qs( 0 ), oc( 0 ).children( aux1 ).head, qs( 1 ), oc( 1 ).children( aux2 ).head )

          case NegLeftRule( _, aux )                       => NegLeftRule( qs( 0 ), oc( 0 ).children( aux ).head )
          case NegRightRule( _, aux )                      => NegRightRule( qs( 0 ), oc( 0 ).children( aux ).head )

          case AndLeftRule( _, aux1, aux2 )                => AndLeftRule( qs( 0 ), oc( 0 ).children( aux1 ).head, oc( 0 ).children( aux2 ).head )
          case AndRightRule( _, aux1, _, aux2 )            => AndRightRule( qs( 0 ), oc( 0 ).children( aux1 ).head, qs( 1 ), oc( 1 ).children( aux2 ).head )

          case OrLeftRule( _, aux1, _, aux2 )              => OrLeftRule( qs( 0 ), oc( 0 ).children( aux1 ).head, qs( 1 ), oc( 1 ).children( aux2 ).head )
          case OrRightRule( _, aux1, aux2 )                => OrRightRule( qs( 0 ), oc( 0 ).children( aux1 ).head, oc( 0 ).children( aux2 ).head )

          case ImpLeftRule( _, aux1, _, aux2 )             => ImpLeftRule( qs( 0 ), oc( 0 ).children( aux1 ).head, qs( 1 ), oc( 1 ).children( aux2 ).head )
          case ImpRightRule( _, aux1, aux2 )               => ImpRightRule( qs( 0 ), oc( 0 ).children( aux1 ).head, oc( 0 ).children( aux2 ).head )

          case ForallLeftRule( _, aux, formula, term, v )  => ForallLeftRule( qs( 0 ), oc( 0 ).children( aux ).head, formula, term, v )
          case ExistsRightRule( _, aux, formula, term, v ) => ExistsRightRule( qs( 0 ), oc( 0 ).children( aux ).head, formula, term, v )

          case EqualityLeftRule( _, eq, aux, pos )         => EqualityLeftRule( qs( 0 ), oc( 0 ).children( eq ).head, oc( 0 ).children( aux ).head, pos )
          case EqualityRightRule( _, eq, aux, pos )        => EqualityRightRule( qs( 0 ), oc( 0 ).children( eq ).head, oc( 0 ).children( aux ).head, pos )
        }
        ( q, ( q.occConnectors, oc, p.occConnectors ).zipped map { _ * _ * _.inv } reduce { _ + _ } )
    }
  }
}
