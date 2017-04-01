package at.logic.gapt.proofs.lk

import at.logic.gapt.proofs.{ Context, SequentConnector }

object freeCutElimination {
  /**
   * See [[FreeCutElimination.apply()]]
   */
  def apply( proof: LKProof )( implicit ctx: Context ) = {
    ( new FreeCutElimination ).apply( proof )
  }
}

/**
 * Free-cut elimination for proofs with equality and induction.
 * @param ctx Defines constants, types, etc.
 */
class FreeCutElimination( implicit val ctx: Context ) {

  /**
   * Eliminates free-cuts with respect to induction inferences and equality rules.
   * @param proof The proof to which the transformation is applied.
   * @return A proof which does not contain any free-cuts.
   */
  def apply( proof: LKProof ): LKProof = visitor.apply( proof, () )

  private object visitor extends LKVisitor[Unit] {
    override protected def recurse( proof: LKProof, arg: Unit ): ( LKProof, SequentConnector ) =
      proof match {
        case CutRule( _, _, _, _ ) =>
          val ( tempProof, tempConnector ) = super.recurse( proof, () )
          cutReduction( tempProof ) match {
            case Some( newProof ) =>
              val ( finalProof, _ ) = super.recurse( newProof, () )
              ( finalProof, SequentConnector.guessInjection( finalProof.conclusion, proof.conclusion ).inv )
            case None => ( tempProof, tempConnector )
          }
        case _ => super.recurse( proof, () )
      }
  }

  private def cutReduction( proof: LKProof ): Option[LKProof] = proof match {
    case cut @ CutRule( _, _, _, _ ) =>
      gradeReduction( cut )
        .orElse( leftRankReduction( cut ) )
        .orElse( rightRankReduction( cut ) )
        .orElse( inductionReduction( cut ) )
    case _ => None
  }

}
