package at.logic.gapt.proofs.lk

import at.logic.gapt.expr.isConstructorForm
import at.logic.gapt.proofs.lk.cutFree.nonCommutingCutReduction
import at.logic.gapt.proofs.{Context, SequentConnector}
import at.logic.gapt.proofs.lk.reductions._

object inductionFree {
  /**
   * Transforms a proof to a proof without induction inferences.
   *
   * @param proof The proof to which the transformation is applied.
   * @param ctx Defines constants, types, etc.
   * @return A proof obtained by repeated application of induction unfolding; equality reduction and free-cut
   *         elimination. The reduction ends if there is no more unfoldable induction i.e. there is no induction
   *         inference with constructor form induction term. If the input proof does not have a sigma 1 end-sequent,
   *         or contains Skolem quantifier inferences, then the returned proof may contain induction inferences.
   */
  def apply( proof: LKProof )( implicit ctx: Context ): LKProof = {
    var newProof = proof
    var done = false
    do {
      newProof = pushEqualityInferencesToLeaves( newProof )
      newProof = freeCutFree( newProof )
      val inductionUnfolder = new UnfoldInductions
      newProof = inductionUnfolder( newProof )
      done = inductionUnfolder.unfoldedInduction
    } while ( !done )
    newProof
  }
}

object freeCutFree {
  /**
   * See [[FreeCutElimination.apply]]
   */
  def apply( proof: LKProof )( implicit ctx: Context ) = {
    ( new FreeCutElimination ).apply( proof )
  }
}

class FreeCutReduction( implicit val ctx: Context) {

  val nonCommutingRightRankReduction =
    RightRankWeakeningLeftReduction orElse
    RightRankWeakeningRightReduction orElse
    RightRankContractionLeftReduction orElse
    RightRankContractionRightReduction orElse
    RightRankDefinitionLeftReduction orElse
    RightRankDefinitionRightReduction orElse
    RightRankAndLeftReduction orElse
    RightRankAndRightReduction orElse
    RightRankOrLeftReduction orElse
    RightRankOrRightReduction orElse
    RightRankImpLeftReduction orElse
    RightRankImpRightReduction orElse
    RightRankNegLeftReduction orElse
    RightRankNegRightReduction orElse
    RightRankForallLeftReduction orElse
    RightRankForallRightReduction orElse
    RightRankForallSkRightReduction orElse
    RightRankExistsLeftReduction orElse
    RightRankExistsSkLeftReduction orElse
    RightRankExistsRightReduction orElse
    RightRankEqualityLeftReduction orElse
    RightRankEqualityRightReduction orElse
    RightRankInductionReduction

  val nonCommutingLeftRankReduction =
    LeftRankWeakeningLeftReduction orElse
    LeftRankWeakeningRightReduction orElse
    LeftRankContractionLeftReduction orElse
    LeftRankContractionRightReduction orElse
    LeftRankDefinitionLeftReduction orElse
    LeftRankDefinitionRightReduction orElse
    LeftRankAndLeftReduction orElse
    LeftRankAndRightReduction orElse
    LeftRankOrLeftReduction orElse
    LeftRankOrRightReduction orElse
    LeftRankImpLeftReduction orElse
    LeftRankImpRightReduction orElse
    LeftRankNegLeftReduction orElse
    LeftRankNegRightReduction orElse
    LeftRankForallLeftReduction orElse
    LeftRankForallRightReduction orElse
    LeftRankForallSkRightReduction orElse
    LeftRankExistsLeftReduction orElse
    LeftRankExistsSkLeftReduction orElse
    LeftRankExistsRightReduction orElse
    LeftRankEqualityLeftReduction orElse
    LeftRankEqualityRightReduction orElse
    LeftRankInductionReduction

  val commutingCutReduction =
    LeftRankCutInductionReduction orElse
  RightRankCutInductionReduction orElse
  LeftRankCutEqualityRightLeftReduction orElse
  LeftRankCutEqualityRightRightReduction orElse
  LeftRankCutEqualityLeftRightReduction orElse
  RightRankCutEqualityLeftRightReduction orElse
  RightRankCutEqualityRightLeftReduction orElse
  RightRankCutEqualityRightRightReduction orElse
  LeftRankCutCutEqualityRightReduction orElse
  LeftRankCutCutEqualityLeftReduction orElse
  RightRankCutCutEqualityLeftReduction orElse
  RightRankCutCutEqualityRightReduction


  val nonCommutingCutReduction =
    gradeReduction orElse
    nonCommutingLeftRankReduction orElse
    nonCommutingRightRankReduction

  val cutReduction =
    nonCommutingCutReduction orElse commutingCutReduction orElse (new LeftRankInductionUnfoldingReduction())

  def apply(proof: LKProof): LKProof
    = new UppermostFirstStrategy( cutReduction ) run proof
}

class LeftRankInductionUnfoldingReduction(implicit ctx: Context) extends CutReduction {
  override def reduce(cut: CutRule): Option[LKProof] = {
    cut.leftSubProof match {
      case ind @ InductionRule(_,_,_) if isConstructorForm(ind.term) =>
        Some(new ParallelAtDepthStrategy(new InductionUnfoldingReduction(), 1) run cut)
      case _ => None
    }
  }
}

object LeftRankCutInductionReduction extends CutReduction {
  override def reduce(cut: CutRule): Option[LKProof] = {
    cut.leftSubProof match {
      case CutRule( InductionRule(_,_,_),_,_,_) => {
        val Some(step1 : LKProof) = LeftRankCutReduction.reduce(cut)
        Some(new ParallelAtDepthStrategy(LeftRankInductionReduction, 1).run(step1))
      }
      case _ => None
    }
  }
}

object RightRankCutInductionReduction extends CutReduction {
  override def reduce(cut: CutRule): Option[LKProof] = {
    cut.rightSubProof match {
      case CutRule(_, _, InductionRule(_, _, _), _) => {
        val Some(step1 : LKProof) = RightRankCutReduction reduce cut
        Some(new ParallelAtDepthStrategy(RightRankInductionReduction, 1) run step1 )
      }
      case _ => None
    }
  }
}

object LeftRankCutEqualityRightLeftReduction extends CutReduction {
  override def reduce(cut: CutRule): Option[LKProof] = {
    cut.leftSubProof match {
      case CutRule(EqualityRightRule(_,_,_,_),_,_,_) => {
        // step 1: push the cut upwards
        val Some(step1 : LKProof) = LeftRankCutReduction reduce cut
        // step 2: push the cut over the equality inference
        Some(new ParallelAtDepthStrategy(LeftRankEqualityRightReduction, 1) run step1)
      }
      case _ => None
    }
  }
}

object LeftRankCutEqualityRightRightReduction extends CutReduction {
  override def reduce(cut: CutRule): Option[LKProof] = {
    cut.leftSubProof match {
      case cut2 @ CutRule(_,_, eq @ EqualityRightRule(_,_,_,_),_
      ) if (cut2.getRightSequentConnector.child(eq.auxInConclusion) != cut.aux1) => {
        val Some(step1 : LKProof) = LeftRankCutReduction reduce cut
        Some(new ParallelAtDepthStrategy(LeftRankEqualityRightReduction, 1) run step1)
      }
      case _ => None
    }
  }
}

object LeftRankCutEqualityLeftRightReduction extends CutReduction {
  override def reduce(cut: CutRule) : Option[LKProof] = {
    cut.leftSubProof match {
      case CutRule(_,_, EqualityLeftRule(_,_,_,_),_) => {
        val Some(step1: LKProof) = LeftRankCutReduction reduce cut
        Some(new ParallelAtDepthStrategy(LeftRankEqualityLeftReduction, 1) run step1)
      }
      case _ => None
    }
  }
}

object RightRankCutEqualityLeftRightReduction extends CutReduction {
  override def reduce(cut: CutRule):Option[LKProof] = {
    cut.rightSubProof match {
      case cut2@CutRule(_, _, eq@EqualityLeftRule(_, _, _, _), _
      ) if cut2.getRightSequentConnector.child(eq.eqInConclusion) != cut.aux2 &&
        cut2.getRightSequentConnector.child(eq.auxInConclusion) != cut.aux2 =>
        val Some(step1 : LKProof) = RightRankCutReduction reduce cut
        Some(new ParallelAtDepthStrategy(RightRankEqualityLeftReduction,1) run step1)
      case _ => None
    }
  }
}

object RightRankCutEqualityRightLeftReduction extends CutReduction {
  override def reduce(cut: CutRule) :Option[LKProof] = {
    cut.rightSubProof match {
      case cut2@CutRule(eq@EqualityRightRule(_, _, _, _), _, _, _
      ) if (cut2.getLeftSequentConnector.child(eq.eqInConclusion) != cut.aux2) =>
        val Some(step1: LKProof) = RightRankCutReduction reduce cut
        Some(new ParallelAtDepthStrategy(RightRankEqualityRightReduction, 1) run step1)
      case _ => None
    }
  }
}

object RightRankCutEqualityRightRightReduction extends CutReduction {
  override def reduce(cut: CutRule): Option[LKProof] = {
    cut.rightSubProof match {
      case CutRule(_,_,EqualityRightRule(_,_,_,_),_) =>
        val Some(step1: LKProof) = RightRankCutReduction reduce cut
        Some(new ParallelAtDepthStrategy(RightRankEqualityRightReduction, 1) run step1)
      case _ => None
    }
  }
}

object LeftRankCutCutEqualityRightReduction extends CutReduction {
  override def reduce(cut: CutRule): Option[LKProof] = {
    cut.leftSubProof match {
      case CutRule(CutRule(_,_,EqualityRightRule(_,_,_,_),_),_,_,_) |
           CutRule(_,_,CutRule(EqualityRightRule(_,_,_,_),_,_,_),_) => {
        val Some(step1 : LKProof) = LeftRankCutReduction reduce cut
        val step2: LKProof = new ParallelAtDepthStrategy(LeftRankCutReduction, 1) run step1
        Some (new ParallelAtDepthStrategy(LeftRankEqualityRightReduction, 2) run step2)
      }
      case _ => None
    }
  }
}

object LeftRankCutCutEqualityLeftReduction extends CutReduction {
  override def reduce(cut: CutRule) : Option[LKProof] = {
    cut.leftSubProof match {
      case CutRule(_,_,CutRule(_,_,EqualityLeftRule(_,_,_,_),_),_) =>
        val Some(step1: LKProof) = LeftRankCutReduction reduce cut
        val step2 : LKProof = new ParallelAtDepthStrategy(LeftRankCutReduction, 1) run step1
        Some( new ParallelAtDepthStrategy(LeftRankEqualityLeftReduction, 2) run step2)
      case _ => None
    }
  }
}

object RightRankCutCutEqualityLeftReduction extends CutReduction {
  override def reduce(cut: CutRule): Option[LKProof] = {
    cut.rightSubProof match {
      case CutRule(_,_,CutRule(_,_,EqualityLeftRule(_,_,_,_),_),_) =>
        val Some(step1: LKProof) = RightRankCutReduction reduce cut
        val step2 : LKProof = new ParallelAtDepthStrategy(RightRankCutReduction, 1) run step1
        Some(new ParallelAtDepthStrategy(RightRankEqualityLeftReduction, 2) run step2)
      case _ => None
    }
  }
}

object RightRankCutCutEqualityRightReduction extends CutReduction {
  override def reduce(cut: CutRule): Option[LKProof] = {
    cut.rightSubProof match {
      case CutRule(CutRule(_,_,EqualityRightRule(_,_,_,_),_),_,_,_) |
           CutRule(_,_,CutRule(EqualityRightRule(_,_,_,_),_,_,_),_) =>
        val Some(step1: LKProof) = RightRankCutReduction reduce cut
        val step2: LKProof = new ParallelAtDepthStrategy(RightRankCutReduction, 1) run step1
        Some(new ParallelAtDepthStrategy(RightRankEqualityRightReduction, 2) run step2)
      case _ => None
    }
  }
}

// todo: skolem quantifier rules

/**
 * Free-cut elimination for proofs with equality and induction.
 * @param ctx Defines constants, types, etc.
 */
class FreeCutElimination( implicit val ctx: Context ) {

  /**
   * Eliminates free-cuts with respect to induction inferences and equality rules.
   * @param proof The proof to which the transformation is applied.
   * @return A proof which does not contain any free-cuts, if the input proof does
   *         not contain Skolem quantifier inferences.
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

class UnfoldInductions( implicit ctx: Context ) {
  val reductionStrategy = new IterativeParallelStrategy( new InductionUnfoldingReduction() )

  /**
   * Unfolds all unfoldable induction inferences.
   * @param proof The proof in which the induction inferences are unfolded.
   * @return A proof which does not contain unfoldable induction inferences.
   */
  def apply( proof: LKProof ): LKProof =
    reductionStrategy.run( proof )
  def unfoldedInduction = reductionStrategy.appliedReduction
}