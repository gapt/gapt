package at.logic.gapt.proofs.lk

import at.logic.gapt.proofs.expansion.{ ExpansionProofToLK, ExpansionProofWithCut, deskolemizeET, eliminateCutsET }
import at.logic.gapt.proofs.{ Ant, SequentConnector, Suc }

object addCutsBelowSkolemInferences extends LKVisitor[Unit] {

  def apply( p: LKProof ): LKProof = apply( p, () )

  override protected def visitForallSkRight( proof: ForallSkRightRule, otherArg: Unit ): ( CutRule, SequentConnector ) = {
    val ( p, occ ) = super.visitForallSkRight( proof, otherArg )
    val q = CutRule( p, p.mainIndices.head, LogicalAxiom( p.mainFormulas.head ), Ant( 0 ) )
    ( q, ( q.getLeftSequentConnector * occ ) + ( q.getRightSequentConnector.child( Suc( 0 ) ), proof.mainIndices.head ) )
  }

  override protected def visitExistsSkLeft( proof: ExistsSkLeftRule, otherArg: Unit ): ( CutRule, SequentConnector ) = {
    val ( p, occ ) = super.visitExistsSkLeft( proof, otherArg )
    val q = CutRule( LogicalAxiom( p.mainFormulas.head ), Suc( 0 ), p, p.mainIndices.head )
    ( q, q.getRightSequentConnector * occ + ( q.getLeftSequentConnector.child( Ant( 0 ) ), proof.mainIndices.head ) )
  }
}

object deskolemizeLK {
  def apply( p: LKProof ): LKProof = {
    val p1 = addCutsBelowSkolemInferences( p )
    val p2 = LKToExpansionProof( p1 )
    val p3 = eliminateCutsET( p2 )
    val p4 = deskolemizeET( p3 )
    val p5 = eliminateCutsET( ExpansionProofWithCut( p4 ) )
    val Right( p6 ) = ExpansionProofToLK( p5 )
    p6
  }
}