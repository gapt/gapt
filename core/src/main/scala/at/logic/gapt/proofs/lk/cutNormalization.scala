package at.logic.gapt.proofs.lk

import at.logic.gapt.proofs.SequentConnector

trait Reduction {
  def reduce( proof: LKProof ): Option[LKProof]
  def orElse( reduction: Reduction ): Reduction =
    new Reduction {
      def reduce( proof: LKProof ) =
        Reduction.this.reduce( proof ) orElse reduction.reduce( proof )
    }
  def andThen( reduction: Reduction ): Reduction =
    new Reduction {
      def reduce( proof: LKProof ) =
        Reduction.this.reduce( proof ) flatMap reduction.reduce
    }
}

trait CutReduction extends Reduction {
  def reduce( proof: LKProof ): Option[LKProof] =
    proof match {
      case cut @ CutRule( _, _, _, _ ) => reduce( cut )
      case _                           => None
    }
  def reduce( proof: CutRule ): Option[LKProof]
  def orElse( reduction: CutReduction ): CutReduction =
    new CutReduction {
      def reduce( cut: CutRule ) = CutReduction.this.reduce( cut ) orElse reduction.reduce( cut )
    }
  def andThen( reduction: CutReduction ): CutReduction =
    new CutReduction {
      def reduce( cut: CutRule ) = CutReduction.this.reduce( cut ) flatMap reduction.reduce
    }
}

trait ReductionStrategy {
  def transform( reduction: Reduction, proof: LKProof ): LKProof
}

class UppermostRedexReduction( reduction: Reduction ) extends Reduction {
  override def reduce( proof: LKProof ): Option[LKProof] = {
    reduction.reduce( proof ) match {
      case result @ Some( _ ) if !hasUpperRedex( proof ) => result
      case _ => None
    }
  }
  private def hasUpperRedex( proof: LKProof ) = {
    proof.immediateSubProofs.exists( isRedex( _, reduction ) )
  }

  private def isRedex( proof: LKProof, reduction: Reduction ): Boolean =
    reduction.reduce( proof ).nonEmpty
}

object uppermostFirstStrategy extends ReductionStrategy {
  def transform( reduction: Reduction, proof: LKProof ): LKProof = {
    new LKVisitor[Unit] {
      override def recurse( proof: LKProof, u: Unit ): ( LKProof, SequentConnector ) = {
        val ( intermediaryProof, intermediaryConnector ): ( LKProof, SequentConnector ) = super.recurse( proof, u )
        reduction.reduce( intermediaryProof ) match {
          case Some( intermediaryProof2 ) => {
            val ( finalProof, _ ): ( LKProof, SequentConnector ) = recurse( intermediaryProof2, u )
            ( finalProof, SequentConnector.guessInjection(
              fromLower = proof.conclusion, toUpper = finalProof.conclusion ).inv )
          }
          case None => ( intermediaryProof, intermediaryConnector )
        }
      }
    }.apply( proof, () )
  }
}

object iterativeParallelStrategy extends ReductionStrategy {
  override def transform( reduction: Reduction, proof: LKProof ): LKProof = {
    var intermediaryProof = proof
    var reduced = false
    do {
      reduced = false
      intermediaryProof = new LKVisitor[Unit] {
        override def recurse( proof: LKProof, u: Unit ): ( LKProof, SequentConnector ) = {
          reduction.reduce( proof ) match {
            case Some( finalProof ) =>
              reduced = true
              ( finalProof, SequentConnector.guessInjection(
                fromLower = proof.conclusion, toUpper = finalProof.conclusion ).inv )
            case _ => super.recurse( proof, u )
          }
        }
      }.apply( intermediaryProof, () )
    } while ( reduced )
    intermediaryProof
  }
}

class IterativeSelectiveStrategy( selector: ( LKProof ) => Option[LKProof] ) extends ReductionStrategy {
  override def transform( reduction: Reduction, proof: LKProof ): LKProof = {
    var intermediaryProof = proof
    var continue = false
    do {
      continue = false
      selector( intermediaryProof ) match {
        case Some( redex ) =>
          continue = true
          intermediaryProof = new SelectiveProofReducer( reduction, redex ).apply( intermediaryProof, () )
        case None =>
      }
    } while ( continue )
    intermediaryProof
  }

  // todo: This might reduce several redexes at once.
  // We want to select an occurrence of a cut and not a cut itself.
  // Hence it might be better to use the path to the cut.
  private class SelectiveProofReducer( reduction: Reduction, redex: LKProof ) extends LKVisitor[Unit] {
    override def recurse( proof: LKProof, u: Unit ): ( LKProof, SequentConnector ) = {
      if ( proof == redex ) {
        reduction.reduce( proof ) match {
          case Some( newProof ) =>
            ( newProof, SequentConnector.guessInjection(
              fromLower = proof.conclusion, toUpper = newProof.conclusion ).inv )
          case _ => throw new IllegalStateException( "redex must be reducible" )
        }
      } else {
        super.recurse( proof, u )
      }
    }
  }
}

object cutElimination {
  def apply( proof: LKProof ): LKProof =
    uppermostFirstStrategy.transform( nonCommutingCutReduction, proof )
}

object nonCommutingCutReduction extends CutReduction {

  override def reduce( cut: CutRule ): Option[LKProof] = reduction.reduce( cut )

  def reduction = gradeReduction orElse
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
    RightRankEqualityRightReduction orElse leftRankReduction
}
