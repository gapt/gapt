package at.logic.gapt.proofs.lk

import at.logic.gapt.proofs.{Context, SequentConnector}
import at.logic.gapt.proofs.lk.reductions._

object freeCutFree {
  /**
    * See [[FreeCutElimination.apply]]
    */
  def apply( proof: LKProof )( implicit ctx: Context ) = {
    ( new FreeCutElimination ).apply( proof )
  }
}

object isFreeCutFree {
  def apply(proof: LKProof): Boolean = ???
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
    override protected def recurse( proof: LKProof, arg: Unit ): ( LKProof, SequentConnector ) = {
      proof match {
        case CutRule( _, _, _, _ ) => {
          val ( tempProof, tempConnector ) = super.recurse( proof, () )
          reduction( tempProof ) match {
            case Some( ( newProof, _ ) ) =>
              ( newProof, SequentConnector.guessInjection(
                fromLower = proof.conclusion, toUpper = newProof.conclusion ).inv )
            case None => ( tempProof, tempConnector )
          }
        }
        case _ => super.recurse( proof, () )
      }
    }

    private def weakeningEqualityOnlyTree( proof: LKProof ) = proof.subProofs.forall {
      case EqualityRightRule( _, _, _, _ ) => true
      case EqualityLeftRule( _, _, _, _ )  => true
      case WeakeningRightRule( _, _ )      => true
      case WeakeningLeftRule( _, _ )       => true
      case InitialSequent( _ )             => true
      case _                               => false
    }

    private def recurseGradeReduction( cut: CutRule ): Option[( LKProof, SequentConnector )] =
      gradeReduction( cut ) map { recurse( _, () ) }

    private def recurseLeftRankReduction( cut: CutRule ): Option[( LKProof, SequentConnector )] =
      leftRankReduction( cut ) map { super.recurse( _, () ) }

    private def recurseRightRankReduction( cut: CutRule ): Option[( LKProof, SequentConnector )] =
      rightRankReduction( cut ) map { super.recurse( _, () ) }

    private def recurseInductionReduction( cut: CutRule ): Option[( LKProof, SequentConnector )] =
      ( LeftRankInductionReduction orElse RightRankInductionReduction ).reduce( cut ) map { super.recurse( _, () ) }

    private def reduction( proof: LKProof ): Option[( LKProof, SequentConnector )] = {
      val cut @ CutRule( _, _, _, _ ) = proof
      ( cut.leftSubProof, cut.rightSubProof ) match {
        case ( EqualityLeftRule( _, _, _, _ ), EqualityLeftRule( _, _, _, _ ) )
             | ( EqualityLeftRule( _, _, _, _ ), EqualityRightRule( _, _, _, _ ) )
             | ( EqualityRightRule( _, _, _, _ ), EqualityLeftRule( _, _, _, _ ) )
             | ( EqualityRightRule( _, _, _, _ ), EqualityRightRule( _, _, _, _ )
               ) if weakeningEqualityOnlyTree( cut.leftSubProof ) && weakeningEqualityOnlyTree( cut.rightSubProof ) =>
          recurseGradeReduction( cut )
        case ( EqualityLeftRule( _, _, _, _ ), _ )
             | ( EqualityRightRule( _, _, _, _ ), _ ) if weakeningEqualityOnlyTree( cut.leftSubProof ) =>
          recurseGradeReduction( cut ) orElse recurseRightRankReduction( cut ) orElse recurseInductionReduction( cut )
        case ( _, EqualityLeftRule( _, _, _, _ ) )
             | ( _, EqualityRightRule( _, _, _, _ ) ) if weakeningEqualityOnlyTree( cut.rightSubProof ) =>
          recurseGradeReduction( cut ) orElse recurseLeftRankReduction( cut ) orElse recurseInductionReduction( cut )
        case ( _, _ ) =>
          recurseGradeReduction( cut )
            .orElse( recurseRightRankReduction( cut ) )
            .orElse( recurseLeftRankReduction( cut ) )
            .orElse( recurseInductionReduction( cut ) )
      }
    }
  }
}

object unfoldInductions {
  def apply( proof: LKProof )( implicit ctx: Context ): LKProof =
    (new IterativeParallelStrategy(new InductionUnfoldingReduction())).run(proof)
}