package gapt.proofs.lk

import gapt.expr.{ Polarity, isConstructorForm }
import gapt.proofs.{ Context, SequentConnector, SequentIndex }
import gapt.proofs.lk.reductions._
import gapt.prooftool.prooftool

object cutNormal {
  def apply(
    proof:                LKProof,
    cleanStructuralRules: Boolean = true,
    unfoldInductions:     Boolean = false )( implicit ctx: Context = Context.default ) =
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
      new IterativeParallelCsrStrategy( cutReduction, 1002 ) run proof
    else
      new UppermostFirstStrategy( cutReduction ) run proof
  }

  /**
   * Implements an iterative parallel reduction, that cleans structural rules after each iteration.
   * @param reduction The reduction to be used by this strategy
   */
  private class IterativeParallelCsrStrategy( reduction: Reduction, var steps: Int ) extends ReductionStrategy {
    override def run( proof: LKProof ): LKProof = {
      var intermediaryProof = proof
      val reducer = ( new LowerMostRedexReducer( ( new UppermostRedexFilter ).filter( reduction ) ) )
      do {
        reducer.foundRedex = false
        intermediaryProof = reducer.apply( intermediaryProof, () )
        intermediaryProof = gapt.proofs.lk.cleanStructuralRules( intermediaryProof )
        steps -= 1
      } while ( reducer.foundRedex && steps > 0 )
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
              val newConnector = SequentConnector.guessInjection(
                fromLower = newProof.conclusion, toUpper = cut.leftSubProof.conclusion )
              CutRule( newProof, newConnector.child( cut.aux1 ), cut.rightSubProof, cut.aux2 )
            }
          case None =>
            for {
              newProof <- moveCut(
                polarity, left, aux, cut.getRightSequentConnector.parent( rightCutFormulaIndex ), cut.rightSubProof )
            } yield {
              val newConnector =
                SequentConnector.guessInjection(
                  fromLower = newProof.conclusion, toUpper = cut.rightSubProof.conclusion )
              CutRule( cut.leftSubProof, cut.aux1, newProof, newConnector.child( cut.aux2 ) )
            }
        }
      case p @ _ => cutNormal.nonCommutingCutReduction.reduce(
        polarity match {
          case false => CutRule( left, aux, p, rightCutFormulaIndex )
          case true  => CutRule( p, rightCutFormulaIndex, left, aux )
        } )
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

object LeftRankCutInductionReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] = {
    cut.leftSubProof match {
      case CutRule( InductionRule( _, _, _ ), _, _, _ ) => {
        val Some( step1: LKProof ) = LeftRankCutReduction.reduce( cut )
        Some( new ParallelAtDepthStrategy( LeftRankInductionReduction, 1 ).run( step1 ) )
      }
      case _ => None
    }
  }
}

object RightRankCutInductionReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] = {
    cut.rightSubProof match {
      case CutRule( InductionRule( _, _, _ ), _, _, _ ) => {
        val Some( step1: LKProof ) = RightRankCutReduction reduce cut
        Some( new ParallelAtDepthStrategy( RightRankInductionReduction, 1 ) run step1 )
      }
      case _ => None
    }
  }
}

object LeftRankCutEqualityRightLeftReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] = {
    cut.leftSubProof match {
      case CutRule( EqualityRightRule( _, _, _, _ ), _, _, _ ) => {
        // step 1: push the cut upwards
        val Some( step1: LKProof ) = LeftRankCutReduction reduce cut
        // step 2: push the cut over the equality inference
        Some( new ParallelAtDepthStrategy( LeftRankEqualityRightReduction, 1 ) run step1 )
      }
      case _ => None
    }
  }
}

object LeftRankCutEqualityRightRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] = {
    cut.leftSubProof match {
      case cut2 @ CutRule( _, _, eq @ EqualityRightRule( _, _, _, _ ), _
        ) if !cut2.getRightSequentConnector.children( eq.auxInConclusion ).contains( cut.aux1 ) => {
        val Some( step1: LKProof ) = LeftRankCutReduction reduce cut
        Some( new ParallelAtDepthStrategy( LeftRankEqualityRightReduction, 1 ) run step1 )
      }
      case _ => None
    }
  }
}

object LeftRankCutEqualityLeftRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] = {
    cut.leftSubProof match {
      case CutRule( _, _, EqualityLeftRule( _, _, _, _ ), _ ) => {
        val Some( step1: LKProof ) = LeftRankCutReduction reduce cut
        Some( new ParallelAtDepthStrategy( LeftRankEqualityLeftReduction, 1 ) run step1 )
      }
      case _ => None
    }
  }
}

object RightRankCutEqualityLeftRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] = {
    cut.rightSubProof match {
      case cut2 @ CutRule( _, _, eq @ EqualityLeftRule( _, _, _, _ ), _
        ) if !cut2.getRightSequentConnector.children( eq.eqInConclusion ).contains( cut.aux2 ) &&
        !cut2.getRightSequentConnector.children( eq.auxInConclusion ).contains( cut.aux2 ) =>
        val Some( step1: LKProof ) = RightRankCutReduction reduce cut
        Some( new ParallelAtDepthStrategy( RightRankEqualityLeftReduction, 1 ) run step1 )
      case _ => None
    }
  }
}

object RightRankCutEqualityRightLeftReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] = {
    cut.rightSubProof match {
      case cut2 @ CutRule( eq @ EqualityRightRule( _, _, _, _ ), _, _, _
        ) if !cut2.getLeftSequentConnector.children( eq.eqInConclusion ).contains( cut.aux2 ) =>
        val Some( step1: LKProof ) = RightRankCutReduction reduce cut
        Some( new ParallelAtDepthStrategy( RightRankEqualityRightReduction, 1 ) run step1 )
      case _ => None
    }
  }
}

object RightRankCutEqualityRightRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] = {
    cut.rightSubProof match {
      case CutRule( _, _, EqualityRightRule( _, _, _, _ ), _ ) =>
        val Some( step1: LKProof ) = RightRankCutReduction reduce cut
        Some( new ParallelAtDepthStrategy( RightRankEqualityRightReduction, 1 ) run step1 )
      case _ => None
    }
  }
}

object LeftRankCutCutEqualityRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] = {
    cut.leftSubProof match {
      case CutRule( CutRule( _, _, EqualityRightRule( _, _, _, _ ), _ ), _, _, _ ) |
        CutRule( _, _, CutRule( EqualityRightRule( _, _, _, _ ), _, _, _ ), _ ) => {
        val Some( step1: LKProof ) = LeftRankCutReduction reduce cut
        val step2: LKProof = new ParallelAtDepthStrategy( LeftRankCutReduction, 1 ) run step1
        Some( new ParallelAtDepthStrategy( LeftRankEqualityRightReduction, 2 ) run step2 )
      }
      case _ => None
    }
  }
}

object LeftRankCutCutEqualityLeftReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] = {
    cut.leftSubProof match {
      case CutRule( _, _, CutRule( _, _, EqualityLeftRule( _, _, _, _ ), _ ), _ ) =>
        val Some( step1: LKProof ) = LeftRankCutReduction reduce cut
        val step2: LKProof = new ParallelAtDepthStrategy( LeftRankCutReduction, 1 ) run step1
        Some( new ParallelAtDepthStrategy( LeftRankEqualityLeftReduction, 2 ) run step2 )
      case _ => None
    }
  }
}

object RightRankCutCutEqualityLeftReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] = {
    cut.rightSubProof match {
      case CutRule( _, _, CutRule( _, _, EqualityLeftRule( _, _, _, _ ), _ ), _ ) =>
        val Some( step1: LKProof ) = RightRankCutReduction reduce cut
        val step2: LKProof = new ParallelAtDepthStrategy( RightRankCutReduction, 1 ) run step1
        Some( new ParallelAtDepthStrategy( RightRankEqualityLeftReduction, 2 ) run step2 )
      case _ => None
    }
  }
}

object RightRankCutCutEqualityRightReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] = {
    cut.rightSubProof match {
      case CutRule( CutRule( _, _, EqualityRightRule( _, _, _, _ ), _ ), _, _, _ ) |
        CutRule( _, _, CutRule( EqualityRightRule( _, _, _, _ ), _, _, _ ), _ ) =>
        val Some( step1: LKProof ) = RightRankCutReduction reduce cut
        val step2: LKProof = new ParallelAtDepthStrategy( RightRankCutReduction, 1 ) run step1
        Some( new ParallelAtDepthStrategy( RightRankEqualityRightReduction, 2 ) run step2 )
      case _ => None
    }
  }
}

object LeftRankCutForallSkReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] = {
    cut.leftSubProof match {
      case CutRule( ForallSkRightRule( _, _, _, _, _ ), _, _, _ ) =>
        val Some( step1: LKProof ) = LeftRankCutReduction reduce cut
        Some( new ParallelAtDepthStrategy( LeftRankForallSkRightReduction, 1 ) run step1 )
    }
  }
}

object LeftRankCutExistsSkReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] = {
    cut.leftSubProof match {
      case CutRule( _, _, ExistsSkLeftRule( _, _, _, _, _ ), _ ) =>
        val Some( step1: LKProof ) = LeftRankCutReduction reduce cut
        Some( new ParallelAtDepthStrategy( LeftRankExistsSkLeftReduction, 1 ) run step1 )
    }
  }
}

object RightRankCutForallSkReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] = {
    cut.rightSubProof match {
      case CutRule( ForallSkRightRule( _, _, _, _, _ ), _, _, _ ) =>
        val Some( step1: LKProof ) = RightRankCutReduction reduce cut
        Some( new ParallelAtDepthStrategy( RightRankForallSkRightReduction, 1 ) run step1 )
    }
  }
}

object RightRankCutExistsSkReduction extends CutReduction {
  override def reduce( cut: CutRule ): Option[LKProof] = {
    cut.rightSubProof match {
      case CutRule( _, _, ExistsSkLeftRule( _, _, _, _, _ ), _ ) =>
        val Some( step1: LKProof ) = RightRankCutReduction reduce cut
        Some( new ParallelAtDepthStrategy( RightRankExistsSkLeftReduction, 1 ) run step1 )
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