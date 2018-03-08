package at.logic.gapt.proofs.lk

import at.logic.gapt.expr.isConstructorForm
import at.logic.gapt.proofs.Context
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
    var continue = false
    do {
      continue = false
      newProof = pushEqualityInferencesToLeaves( newProof )
      newProof = freeCutFree( newProof )
      val inductionUnfolder = new UnfoldInductions
      newProof = inductionUnfolder( newProof )
      continue = inductionUnfolder.unfoldedInduction
    } while ( continue )
    newProof
  }
}

object freeCutFree {
  def apply(proof: LKProof)(implicit ctx: Context) = (new FreeCutReduction).apply(proof)
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
    nonCommutingCutReduction orElse
      commutingCutReduction orElse
      new LeftRankInductionUnfoldingReduction

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

object LeftRankCutForallSkReduction extends CutReduction {
  override def reduce(cut: CutRule): Option[LKProof] = {
    cut.leftSubProof match {
      case CutRule(ForallSkRightRule(_,_,_,_,_),_,_,_) =>
        val Some(step1: LKProof) = LeftRankCutReduction reduce cut
        Some(new ParallelAtDepthStrategy(LeftRankForallSkRightReduction, 1) run step1)
    }
  }
}

object LeftRankCutExistsSkReduction extends CutReduction {
  override def reduce(cut: CutRule): Option[LKProof] = {
    cut.leftSubProof match {
      case CutRule(_,_,ExistsSkLeftRule(_,_,_,_,_),_) =>
        val Some(step1: LKProof) = LeftRankCutReduction reduce cut
        Some(new ParallelAtDepthStrategy(LeftRankExistsSkLeftReduction, 1) run step1)
    }
  }
}

object RightRankCutForallSkReduction extends CutReduction {
  override def reduce(cut: CutRule): Option[LKProof] = {
    cut.rightSubProof match {
      case CutRule(ForallSkRightRule(_,_,_,_,_),_,_,_) =>
        val Some(step1: LKProof) = RightRankCutReduction reduce cut
        Some(new ParallelAtDepthStrategy(RightRankForallSkRightReduction, 1) run step1)
    }
  }
}

object RightRankCutExistsSkReduction extends CutReduction {
  override def reduce(cut: CutRule): Option[LKProof] = {
    cut.rightSubProof match {
      case CutRule(_,_,ExistsSkLeftRule(_,_,_,_,_),_) =>
        val Some(step1: LKProof) = RightRankCutReduction reduce cut
        Some(new ParallelAtDepthStrategy(RightRankExistsSkLeftReduction, 1) run step1)
    }
  }
}


// todo: skolem quantifier rules

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