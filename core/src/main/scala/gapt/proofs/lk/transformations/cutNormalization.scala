package gapt.proofs.lk.transformations

import gapt.expr.isConstructorForm
import gapt.proofs.SequentIndex
import gapt.proofs.context.Context
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.reductions._
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.InductionRule
import gapt.proofs.lk.transformations

object cutNormal {
  def apply(
    proof:                LKProof,
    cleanStructuralRules: Boolean = true,
    unfoldInductions:     Boolean = false )( implicit ctx: Context = Context.default ): LKProof =
    ( new ReductiveCutNormalization( cleanStructuralRules, unfoldInductions ) ).apply( proof )

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

  val nonCommutingCutReduction =
    gradeReduction orElse
      nonCommutingLeftRankReduction orElse
      nonCommutingRightRankReduction

  val commutingCutReduction =
    StuckCutReduction.Right orElse
      StuckCutReduction.Left
}

/**
 * This class implements a version of Gentzen's cut-reduction
 * procedure for our sequent calculus LK.
 */
class ReductiveCutNormalization(
    cleanStructuralRules: Boolean = false,
    unfoldInduction:      Boolean = false )( implicit val ctx: Context ) {

  val cutReduction =
    cutNormal.nonCommutingCutReduction orElse
      cutNormal.commutingCutReduction orElse (
        if ( unfoldInduction )
          new LeftRankInductionUnfoldingReduction
        else
          emptyCutReduction )

  object emptyCutReduction extends CutReduction {
    override def reduce( proof: CutRule ): Option[LKProof] = None
  }

  /**
   * Applies Gentzen's reductive cut-elimination to a proof.
   * @param proof The proof that is subject to cut-elimination.
   * @return If the input proof is an LK proof, then a cut-free proof is returned, otherwise the resulting proof
   *         may not be cut-free.
   */
  def apply( proof: LKProof ): LKProof = {
    if ( cleanStructuralRules )
      new IterativeParallelCsrStrategy( cutReduction ) run proof
    else
      new UppermostFirstStrategy( cutReduction ) run proof
  }

  /**
   * Implements an iterative parallel reduction, that cleans structural rules after each iteration.
   * @param reduction The reduction to be used by this strategy
   */
  private class IterativeParallelCsrStrategy( reduction: Reduction ) extends ReductionStrategy {
    override def run( proof: LKProof ): LKProof = {
      var intermediaryProof = proof
      val reducer = ( new LowerMostRedexReducer( ( new UppermostRedexFilter ).filter( reduction ) ) )
      do {
        reducer.foundRedex = false
        intermediaryProof = reducer.apply( intermediaryProof )
        intermediaryProof = transformations.cleanStructuralRules( intermediaryProof )
      } while ( reducer.foundRedex )
      intermediaryProof
    }
  }
}

object StuckCutReduction {

  object Right extends CutReduction {
    override def reduce( cut: CutRule ): Option[LKProof] = {
      cut.rightSubProof match {
        case CutRule( _, _, _, _ ) =>
          moveCut( false, cut.leftSubProof, cut.aux1, cut.aux2, cut.rightSubProof )
        case _ => None
      }
    }
  }

  object Left extends CutReduction {
    override def reduce( cut: CutRule ): Option[LKProof] = {
      cut.leftSubProof match {
        case CutRule( _, _, _, _ ) =>
          moveCut( true, cut.rightSubProof, cut.aux2, cut.aux1, cut.leftSubProof )
        case _ => None
      }
    }
  }

  def moveCut(
    polarity:             Boolean,
    left:                 LKProof,
    aux:                  SequentIndex,
    rightCutFormulaIndex: SequentIndex,
    stuckCuts:            LKProof ): Option[LKProof] = {
    stuckCuts match {
      case cut @ CutRule( _, _, _, _ ) =>
        cut.getLeftSequentConnector.parentOption( rightCutFormulaIndex ) match {
          case Some( parentFormulaIndex ) =>
            for {
              newProof <- moveCut(
                polarity, left, aux, parentFormulaIndex, cut.leftSubProof )
            } yield {
              CutRule( newProof, cut.rightSubProof, cut.cutFormula )
            }
          case None =>
            for {
              newProof <- moveCut(
                polarity, left, aux, cut.getRightSequentConnector.parent( rightCutFormulaIndex ), cut.rightSubProof )
            } yield {
              CutRule( cut.leftSubProof, newProof, cut.cutFormula )
            }
        }
      case p @ _ => {
        polarity match {
          // cut from left side [=> A] A,X => Y
          case false =>
            val cut = CutRule( left, aux, p, rightCutFormulaIndex )
            for {
              newProof <- cutNormal.nonCommutingCutReduction.reduce( cut )
            } yield {
              newProof
            }
          // cut from right side X => Y, A [A =>]
          case true =>
            val cut = CutRule( p, rightCutFormulaIndex, left, aux )
            for {
              newProof <- cutNormal.nonCommutingCutReduction.reduce( cut )
            } yield {
              newProof
            }
        }
      }
    }
  }
}

class LeftRankInductionUnfoldingReduction( implicit ctx: Context ) extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] = {
    cut.leftSubProof match {
      case ind @ InductionRule( _, _, _ ) if isConstructorForm( ind.term ) =>
        Some( new ParallelAtDepthStrategy( new InductionUnfoldingReduction(), 1 ) run cut )
      case _ => None
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