package at.logic.gapt.proofs.lk

import at.logic.gapt.proofs.{ Ant, OccConnector }

/**
 * Created by sebastian on 21.06.16.
 */

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
        val parentsSequent = p.endSequent.indicesSequent map { Seq( _ ) } delete Ant( 0 ) insertAt ( aux2, Seq( Ant( 0 ) ) )
        val connector = OccConnector( rightSubProof.endSequent, p.endSequent, parentsSequent )
        ( subProofNew, connector * subConnector )

      case ( _, LogicalAxiom( _ ) ) =>
        val ( subProofNew, subConnector ) = recurse( leftSubProof, () )
        val last = p.endSequent.indices.last
        val parentsSequent = p.endSequent.indicesSequent map { Seq( _ ) } delete last insertAt ( aux1, Seq( last ) )
        val connector = OccConnector( leftSubProof.endSequent, p.endSequent, parentsSequent )
        ( subProofNew, connector * subConnector )

      case _ => super.visitCut( p, () )
    }
  }
}
