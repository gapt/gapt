package gapt.proofs.lk

import gapt.proofs._

/**
 * Algorithm that removes some unnecessary cuts.
 * At the moment it only removes cuts where one of the premises is a logical axiom.
 */
object cleanCuts extends LKVisitor[Unit] {

  def apply( p: LKProof ): LKProof = apply( p, () )

  override def visitCut( p: CutRule, otherArg: Unit ) = {
    val CutRule( leftSubProof, aux1, rightSubProof, aux2 ) = p

    ( leftSubProof, rightSubProof ) match {
      case ( LogicalAxiom( _ ), _ ) =>
        val ( subProofNew, subConnector ) = recurse( rightSubProof, () )
        ( subProofNew,
          subConnector * p.getRightSequentConnector.inv
          + ( subConnector.child( aux2 ), p.getLeftSequentConnector.child( Ant( 0 ) ) ) )

      case ( _, LogicalAxiom( _ ) ) =>
        val ( subProofNew, subConnector ) = recurse( leftSubProof, () )
        ( subProofNew,
          subConnector * p.getLeftSequentConnector.inv
          + ( subConnector.child( aux1 ), p.getRightSequentConnector.child( Suc( 0 ) ) ) )

      case _ => super.visitCut( p, () )
    }
  }
}
