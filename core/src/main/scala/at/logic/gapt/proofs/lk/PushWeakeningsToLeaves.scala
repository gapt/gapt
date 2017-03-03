package at.logic.gapt.proofs.lk

import at.logic.gapt.expr.{ HOLFormula, Polarity }

/**
 * Created by cernadavid1 on 01.03.17.
 */
object PushWeakeningToLeaves {
  /**
   * pushes all weakening rules to the leaves of the proof tree and adds contractions to duplications
   *
   * @param proof An LKProof.
   * @return A proof weakening rules at the leaves only.
   */
  def apply( proof: LKProof ): LKProof = proof match {
    case InitialSequent( _ ) => proof

    case WeakeningLeftRule( subProof, formula ) =>
      pushWeakeningToLeaves( subProof, Polarity.Negative, formula )

    case WeakeningRightRule( subProof, formula ) =>
      pushWeakeningToLeaves( subProof, Polarity.Positive, formula )

    case ContractionLeftRule( sb, _, _ ) =>
      ContractionLeftRule( apply( sb ), proof.mainFormulas.head )

    case ContractionRightRule( sb, _, _ ) =>
      ContractionRightRule( apply( sb ), proof.mainFormulas.head )

    case AndRightRule( leftSubProof, _, rightSubProof, _ ) =>
      AndRightRule( apply( leftSubProof ), apply( rightSubProof ), proof.mainFormulas.head )

    case AndLeftRule( subProof, _, _ ) =>
      AndLeftRule( apply( subProof ), proof.mainFormulas.head )

    case OrLeftRule( leftSubProof, _, rightSubProof, _ ) =>
      OrLeftRule( apply( leftSubProof ), apply( rightSubProof ), proof.mainFormulas.head )

    case OrRightRule( subProof, _, _ ) =>
      OrRightRule( apply( subProof ), proof.mainFormulas.head )

    case ImpLeftRule( leftSubProof, _, rightSubProof, _ ) =>
      ImpLeftRule( apply( leftSubProof ), apply( rightSubProof ), proof.mainFormulas.head )

    case ImpRightRule( subProof, _, _ ) =>
      ImpRightRule( apply( subProof ), proof.mainFormulas.head )

    case NegLeftRule( subProof, _ ) =>
      NegLeftRule( apply( subProof ), proof.auxFormulas.head.head )

    case NegRightRule( subProof, _ ) =>
      NegRightRule( apply( subProof ), proof.auxFormulas.head.head )

    case ForallLeftRule( subProof, _, _, term, _ ) =>
      ForallLeftRule( apply( subProof ), proof.mainFormulas.head, term )

    case ForallRightRule( subProof, _, eigen, _ ) =>
      ForallRightRule( apply( subProof ), proof.mainFormulas.head, eigen )

    case ExistsLeftRule( subProof, _, eigen, _ ) =>
      ExistsLeftRule( apply( subProof ), proof.mainFormulas.head, eigen )

    case ExistsRightRule( subProof, _, _, term, _ ) =>
      ExistsRightRule( apply( subProof ), proof.mainFormulas.head, term )

    case ForallSkRightRule( subProof, _, _, skTerm, skDef ) =>
      ForallSkRightRule( apply( subProof ), skTerm, skDef )

    case ExistsSkLeftRule( subProof, _, _, skTerm, skDef ) =>
      ExistsSkLeftRule( apply( subProof ), skTerm, skDef )

    case EqualityLeftRule( subProof, _, _, _ ) =>
      EqualityLeftRule( apply( subProof ), proof.auxFormulas.head( 0 ), proof.auxFormulas.head( 1 ), proof.mainFormulas.head )

    case EqualityRightRule( subProof, _, _, _ ) =>
      EqualityRightRule( apply( subProof ), proof.auxFormulas.head( 0 ), proof.auxFormulas.head( 1 ), proof.mainFormulas.head )

    case CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      CutRule( apply( leftSubProof ), leftSubProof.endSequent( aux1 ), apply( rightSubProof ), rightSubProof.endSequent( aux2 ) )

  }

  /**
   * pushes all weakening rules to the leaves of the proof tree and adds contractions to duplications
   *
   * @param proof An LKProof.
   * @param side  The polarity of the weakening rule.
   * @param formula the formula to be weakened.
   *
   * @return A proof weakening rules at the leaves only.
   */
  private def pushWeakeningToLeaves( proof: LKProof, side: Polarity, formula: HOLFormula ): LKProof = proof match {
    case InitialSequent( _ ) =>
      if ( side.inSuc ) WeakeningRightRule( proof, formula )
      else WeakeningLeftRule( proof, formula )

    case WeakeningLeftRule( subProof, formulaPrime ) =>
      if ( weakeningOnlySubTree( subProof ) )
        if ( side.inSuc ) WeakeningRightRule( proof, formula )
        else WeakeningLeftRule( proof, formula )
      else pushWeakeningToLeaves( pushWeakeningToLeaves( subProof, Polarity.Negative, formulaPrime ), side, formula )

    case WeakeningRightRule( subProof, formulaPrime ) =>
      pushWeakeningToLeaves( pushWeakeningToLeaves( subProof, Polarity.Positive, formulaPrime ), side, formula )

    case ContractionLeftRule( sb, _, _ ) =>
      ContractionLeftRule( pushWeakeningToLeaves( sb, side, formula ), proof.mainFormulas.head )

    case ContractionRightRule( sb, _, _ ) =>
      ContractionRightRule( pushWeakeningToLeaves( sb, side, formula ), proof.mainFormulas.head )

    case AndRightRule( leftSubProof, _, rightSubProof, _ ) =>
      val part = AndRightRule( pushWeakeningToLeaves( leftSubProof, side, formula ), pushWeakeningToLeaves( rightSubProof, side, formula ), proof.mainFormulas.head )
      if ( side.inSuc ) ContractionRightRule( part, formula )
      else ContractionLeftRule( part, formula )

    case AndLeftRule( subProof, _, _ ) =>
      AndLeftRule( pushWeakeningToLeaves( subProof, side, formula ), proof.mainFormulas.head )

    case OrLeftRule( leftSubProof, _, rightSubProof, _ ) =>
      val part = OrLeftRule( pushWeakeningToLeaves( leftSubProof, side, formula ), pushWeakeningToLeaves( rightSubProof, side, formula ), proof.mainFormulas.head )
      if ( side.inSuc ) ContractionRightRule( part, formula )
      else ContractionLeftRule( part, formula )

    case OrRightRule( subProof, _, _ ) =>
      OrRightRule( pushWeakeningToLeaves( subProof, side, formula ), proof.mainFormulas.head )

    case ImpLeftRule( leftSubProof, _, rightSubProof, _ ) =>
      val part = ImpLeftRule( pushWeakeningToLeaves( leftSubProof, side, formula ), pushWeakeningToLeaves( rightSubProof, side, formula ), proof.mainFormulas.head )
      if ( side.inSuc ) ContractionRightRule( part, formula )
      else ContractionLeftRule( part, formula )

    case ImpRightRule( subProof, _, _ ) =>
      ImpRightRule( pushWeakeningToLeaves( subProof, side, formula ), proof.mainFormulas.head )

    case NegLeftRule( subProof, _ ) =>
      NegLeftRule( pushWeakeningToLeaves( subProof, side, formula ), proof.auxFormulas.head.head )

    case NegRightRule( subProof, _ ) =>
      NegRightRule( pushWeakeningToLeaves( subProof, side, formula ), proof.auxFormulas.head.head )

    case ForallLeftRule( subProof, _, _, term, _ ) =>
      ForallLeftRule( pushWeakeningToLeaves( subProof, side, formula ), proof.mainFormulas.head, term )

    case ForallRightRule( subProof, _, eigen, _ ) =>
      ForallRightRule( pushWeakeningToLeaves( subProof, side, formula ), proof.mainFormulas.head, eigen )

    case ExistsLeftRule( subProof, _, eigen, _ ) =>
      ExistsLeftRule( pushWeakeningToLeaves( subProof, side, formula ), proof.mainFormulas.head, eigen )

    case ExistsRightRule( subProof, _, _, term, _ ) =>
      ExistsRightRule( pushWeakeningToLeaves( subProof, side, formula ), proof.mainFormulas.head, term )

    case ForallSkRightRule( subProof, _, _, skTerm, skDef ) =>
      ForallSkRightRule( pushWeakeningToLeaves( subProof, side, formula ), skTerm, skDef )

    case ExistsSkLeftRule( subProof, _, _, skTerm, skDef ) =>
      ExistsSkLeftRule( pushWeakeningToLeaves( subProof, side, formula ), skTerm, skDef )

    case EqualityLeftRule( subProof, _, _, _ ) =>
      EqualityLeftRule( pushWeakeningToLeaves( subProof, side, formula ), proof.auxFormulas.head( 0 ), proof.auxFormulas.head( 1 ), proof.mainFormulas.head )

    case EqualityRightRule( subProof, _, _, _ ) =>
      EqualityRightRule( pushWeakeningToLeaves( subProof, side, formula ), proof.auxFormulas.head( 0 ), proof.auxFormulas.head( 1 ), proof.mainFormulas.head )

    case CutRule( leftSubProof, aux1, rightSubProof, aux2 ) =>
      val part = CutRule( pushWeakeningToLeaves( leftSubProof, side, formula ), leftSubProof.endSequent( aux1 ), pushWeakeningToLeaves( rightSubProof, side, formula ), rightSubProof.endSequent( aux2 ) )
      if ( side.inSuc ) ContractionRightRule( part, formula )
      else ContractionLeftRule( part, formula )
  }

  /**
   * Checks if only weakening rules occur.
   *
   * @param proof An LKProof.
   * @return Boolean.
   */
  private def weakeningOnlySubTree( proof: LKProof ): Boolean = proof match {
    case InitialSequent( _ )               => true
    case WeakeningLeftRule( subProof, _ )  => weakeningOnlySubTree( subProof )
    case WeakeningRightRule( subProof, _ ) => weakeningOnlySubTree( subProof )
    case _                                 => false
  }
}
