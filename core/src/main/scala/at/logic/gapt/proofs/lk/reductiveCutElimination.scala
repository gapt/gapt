package at.logic.gapt.proofs.lk

import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.lk.reductions._

/**
 * This object implements a version of Gentzen's cut-elimination
 * proof for our sequent calculus LK. For details, please
 * refer to the documentation of the apply methods.
 */

object cutFree {

  def apply( proof: LKProof, cleanStructuralRules:Boolean = false ): LKProof =
    if (cleanStructuralRules)
      new IterativeParallelCsrStrategy( nonCommutingCutReduction ) run proof
    else
       new UppermostFirstStrategy( nonCommutingCutReduction ) run proof

  private class IterativeParallelCsrStrategy( reduction: Reduction ) extends ReductionStrategy {
    override def run( proof: LKProof ): LKProof = {
      var intermediaryProof = proof
      val reducer = ( new LowerMostRedexReducer( (new UppermostRedexFilter).filter(reduction) ) )
      do {
        reducer.foundRedex = false
        intermediaryProof = reducer.apply( intermediaryProof, () )
        intermediaryProof = cleanStructuralRules(intermediaryProof)
      } while ( reducer.foundRedex )
      intermediaryProof
    }
  }

  private val nonCommutingCutReduction =
    gradeReduction orElse
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
    LeftRankEqualityRightReduction
}

object isCutFree {
  /**
    * This method checks whether a proof is cut-free.
    * @param proof The proof to check for cut-freeness.
    * @return True if proof does not contain the cut rule, False otherwise.
    */
  def isCutFree( proof: LKProof ): Boolean = proof match {
    case InitialSequent( _ ) => true
    case p: CutRule          => false
    case _                   => proof.immediateSubProofs.forall( isCutFree )
  }
}
