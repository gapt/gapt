package gapt.proofs.lk.transformations

import gapt.expr.Formula
import gapt.expr.Polarity
import gapt.proofs.SequentConnector
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.LKVisitor
import gapt.proofs.lk.rules.AndLeftRule
import gapt.proofs.lk.rules.AndRightRule
import gapt.proofs.lk.rules.ContractionLeftRule
import gapt.proofs.lk.rules.ContractionRightRule
import gapt.proofs.lk.rules.CutRule
import gapt.proofs.lk.rules.EqualityLeftRule
import gapt.proofs.lk.rules.EqualityRightRule
import gapt.proofs.lk.rules.ExistsLeftRule
import gapt.proofs.lk.rules.ExistsRightRule
import gapt.proofs.lk.rules.ExistsSkLeftRule
import gapt.proofs.lk.rules.ForallLeftRule
import gapt.proofs.lk.rules.ForallRightRule
import gapt.proofs.lk.rules.ForallSkRightRule
import gapt.proofs.lk.rules.ImpLeftRule
import gapt.proofs.lk.rules.ImpRightRule
import gapt.proofs.lk.rules.InductionRule
import gapt.proofs.lk.rules.InitialSequent
import gapt.proofs.lk.rules.NegLeftRule
import gapt.proofs.lk.rules.NegRightRule
import gapt.proofs.lk.rules.OrLeftRule
import gapt.proofs.lk.rules.OrRightRule
import gapt.proofs.lk.rules.WeakeningLeftRule
import gapt.proofs.lk.rules.WeakeningRightRule
import gapt.proofs.lk.rules.macros.ContractionMacroRule

object weakeningOnlySubTree {
  /**
   * Checks if the a proof consists only of an initial sequent and weakening inferences.
   *
   * @param proof An LK-proof.
   * @return true if the proof consists only of an initial sequent and weakening inferences, otherwise false.
   */
  def apply( proof: LKProof ): Boolean = proof match {
    case InitialSequent( _ )               => true
    case WeakeningLeftRule( subProof, _ )  => weakeningOnlySubTree( subProof )
    case WeakeningRightRule( subProof, _ ) => weakeningOnlySubTree( subProof )
    case _                                 => false
  }
}

object pushAllWeakeningsToLeaves {

  /**
   * Pushes all weakening inferences to the leaves.
   * @param proof An LK-proof to which the transformation is applied.
   * @return A proof in which all weakening inferences occur near the leaves.
   */
  def apply( proof: LKProof ): LKProof = visitor( proof, () )

  private object visitor extends LKVisitor[Unit] {

    override protected def recurse( proof: LKProof, arg: Unit ): ( LKProof, SequentConnector ) = {
      proof match {
        case weakening @ WeakeningLeftRule( _, _ ) =>
          if ( !weakeningOnlySubTree( weakening ) ) {
            val ( newProof, _ ) = recurse( pushSingleWeakeningToLeaves( weakening ), () )
            ( newProof, SequentConnector.guessInjection( proof.conclusion, newProof.conclusion ).inv )
          } else {
            ( proof, SequentConnector( proof.conclusion ) )
          }
        case weakening @ WeakeningRightRule( _, _ ) =>
          if ( !weakeningOnlySubTree( weakening ) ) {
            val ( newProof, _ ) = recurse( pushSingleWeakeningToLeaves( weakening ), () )
            ( newProof, SequentConnector.guessInjection( proof.conclusion, newProof.conclusion ).inv )
          } else {
            ( proof, SequentConnector( proof.conclusion ) )
          }
        case _ => super.recurse( proof, () )
      }
    }

  }
}

object pushSingleWeakeningToLeaves {

  def withConnector( proof: LKProof ): ( LKProof, SequentConnector ) = {
    val newProof = apply( proof )
    ( newProof, SequentConnector.guessInjection( proof.conclusion, newProof.conclusion ).inv )
  }

  /**
   * Pushes a weakening inference to the leaves.
   * @param proof An LK-proof to which the reduction is applied.
   * @return If the last inference is a weakening inference, and this weakening is not
   *         part of a weakening-only subtree then a proof of the same end-sequent obtained by moving
   *         the weakening inference to the leaves is returned. Otherwise the proof is not modified.
   */
  def apply( proof: LKProof ): LKProof = proof match {
    case weakening @ WeakeningLeftRule( _, _ ) =>
      pushSingleWeakeningToLeaves( weakening.subProof, Polarity.Negative, weakening.formula )
    case weakening @ WeakeningRightRule( _, _ ) =>
      pushSingleWeakeningToLeaves( weakening.subProof, Polarity.Positive, weakening.formula )
    case _ => proof
  }

  /**
   * Adds a weakening inference to the leaves of the given proof.
   * @param proof The proof of the end sequent Γ → Δ.
   * @param side The side of the weakening which will be added.
   * @param formula The formula A which is to be introduced by weakenings.
   * @return A proof of the end sequent Γ → Δ, A or A, Γ → Δ depending on the weakening polarity.
   */
  def apply( proof: LKProof, side: Polarity, formula: Formula ): LKProof = proof match {
    case InitialSequent( _ ) =>
      if ( side.inSuc ) WeakeningRightRule( proof, formula )
      else WeakeningLeftRule( proof, formula )

    case weakening @ WeakeningLeftRule( subProof, _ ) =>
      WeakeningLeftRule( pushSingleWeakeningToLeaves( subProof, side, formula ), weakening.formula )

    case weakening @ WeakeningRightRule( subProof, _ ) =>
      WeakeningRightRule( pushSingleWeakeningToLeaves( subProof, side, formula ), weakening.formula )

    case ContractionLeftRule( sb, _, _ ) =>
      ContractionLeftRule( pushSingleWeakeningToLeaves( sb, side, formula ), proof.mainFormulas.head )

    case ContractionRightRule( sb, _, _ ) =>
      ContractionRightRule( pushSingleWeakeningToLeaves( sb, side, formula ), proof.mainFormulas.head )

    case AndRightRule( leftSubProof, _, rightSubProof, _ ) =>
      val part = AndRightRule(
        pushSingleWeakeningToLeaves( leftSubProof, side, formula ),
        pushSingleWeakeningToLeaves( rightSubProof, side, formula ), proof.mainFormulas.head )
      if ( side.inSuc ) ContractionRightRule( part, formula )
      else ContractionLeftRule( part, formula )

    case AndLeftRule( subProof, _, _ ) =>
      AndLeftRule( pushSingleWeakeningToLeaves( subProof, side, formula ), proof.mainFormulas.head )

    case OrLeftRule( leftSubProof, _, rightSubProof, _ ) =>
      val part = OrLeftRule(
        pushSingleWeakeningToLeaves( leftSubProof, side, formula ),
        pushSingleWeakeningToLeaves( rightSubProof, side, formula ), proof.mainFormulas.head )
      if ( side.inSuc ) ContractionRightRule( part, formula )
      else ContractionLeftRule( part, formula )

    case OrRightRule( subProof, _, _ ) =>
      OrRightRule( pushSingleWeakeningToLeaves( subProof, side, formula ), proof.mainFormulas.head )

    case ImpLeftRule( leftSubProof, _, rightSubProof, _ ) =>
      val part = ImpLeftRule(
        pushSingleWeakeningToLeaves( leftSubProof, side, formula ),
        pushSingleWeakeningToLeaves( rightSubProof, side, formula ), proof.mainFormulas.head )
      if ( side.inSuc ) ContractionRightRule( part, formula )
      else ContractionLeftRule( part, formula )

    case ImpRightRule( subProof, _, _ ) =>
      ImpRightRule( pushSingleWeakeningToLeaves( subProof, side, formula ), proof.mainFormulas.head )

    case NegLeftRule( subProof, _ ) =>
      NegLeftRule( pushSingleWeakeningToLeaves( subProof, side, formula ), proof.auxFormulas.head.head )

    case NegRightRule( subProof, _ ) =>
      NegRightRule( pushSingleWeakeningToLeaves( subProof, side, formula ), proof.auxFormulas.head.head )

    case ForallLeftRule( subProof, _, _, term, _ ) =>
      ForallLeftRule( pushSingleWeakeningToLeaves( subProof, side, formula ), proof.mainFormulas.head, term )

    case ForallRightRule( subProof, _, eigen, _ ) =>
      ForallRightRule( pushSingleWeakeningToLeaves( subProof, side, formula ), proof.mainFormulas.head, eigen )

    case ExistsLeftRule( subProof, _, eigen, _ ) =>
      ExistsLeftRule( pushSingleWeakeningToLeaves( subProof, side, formula ), proof.mainFormulas.head, eigen )

    case ExistsRightRule( subProof, _, _, term, _ ) =>
      ExistsRightRule( pushSingleWeakeningToLeaves( subProof, side, formula ), proof.mainFormulas.head, term )

    case ForallSkRightRule( subProof, _, main, skTerm ) =>
      ForallSkRightRule( pushSingleWeakeningToLeaves( subProof, side, formula ), main, skTerm )

    case ExistsSkLeftRule( subProof, _, main, skTerm ) =>
      ExistsSkLeftRule( pushSingleWeakeningToLeaves( subProof, side, formula ), main, skTerm )

    case EqualityLeftRule( subProof, _, _, _ ) =>
      EqualityLeftRule(
        pushSingleWeakeningToLeaves( subProof, side, formula ),
        proof.auxFormulas.head( 0 ), proof.auxFormulas.head( 1 ), proof.mainFormulas.head )

    case eq @ EqualityRightRule( subProof, _, _, _ ) =>
      val newSubProof = pushSingleWeakeningToLeaves( subProof, side, formula )
      val connector = SequentConnector.guessInjection( subProof.conclusion, newSubProof.conclusion ).inv
      EqualityRightRule( newSubProof, connector.child( eq.eq ), connector.child( eq.aux ), eq.replacementContext )

    case CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val part = CutRule(
        pushSingleWeakeningToLeaves( leftSubProof, side, formula ),
        leftSubProof.endSequent( aux1 ),
        pushSingleWeakeningToLeaves( rightSubProof, side, formula ),
        rightSubProof.endSequent( aux2 ) )
      if ( side.inSuc ) ContractionRightRule( part, formula )
      else ContractionLeftRule( part, formula )

    case ind @ InductionRule( _, _, _ ) =>
      val newInductionCases = ind.cases.map {
        inductionCase =>
          val newCaseProof = pushSingleWeakeningToLeaves( inductionCase.proof, side, formula )
          val connector = SequentConnector.guessInjection(
            inductionCase.proof.conclusion,
            newCaseProof.conclusion ).inv
          inductionCase.copy(
            proof = newCaseProof,
            hypotheses = inductionCase.hypotheses.map( connector.child ),
            conclusion = connector.child( inductionCase.conclusion ) )
      }
      ContractionMacroRule(
        ind.copy( cases = newInductionCases ),
        contractionTarget( formula, side, proof ), false )
  }

  private def contractionTarget( formula: Formula, polarity: Polarity, proof: LKProof ) =
    if ( polarity.positive ) proof.conclusion :+ formula
    else formula +: proof.conclusion

}
