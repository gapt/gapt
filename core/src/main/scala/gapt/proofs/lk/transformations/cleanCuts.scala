package gapt.proofs.lk.transformations

import gapt.proofs.Ant
import gapt.proofs.SequentConnector
import gapt.proofs.Suc
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.LKVisitor
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.LogicalAxiom

/**
 * Algorithm that removes some unnecessary cuts.
 * At the moment it only removes cuts where one of the premises is a logical axiom.
 */
object cleanCuts {

  def apply( p: LKProof ): LKProof = cleanCutsVisitor( p, () )

  private object cleanCutsVisitor extends LKVisitor[Unit] {

    override def visitCut( p: CutRule, otherArg: Unit ): ( LKProof, SequentConnector ) = {
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

}
