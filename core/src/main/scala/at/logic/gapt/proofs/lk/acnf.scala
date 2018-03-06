package at.logic.gapt.proofs.lk

import at.logic.gapt.expr.Formula
import at.logic.gapt.expr.hol.isAtom
import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.lk.reductions.{CutReduction, gradeReduction, leftRankReduction, rightRankReduction}

object acnf {
  def apply(proof: LKProof) =
    ( new UppermostFirstStrategy( AcnfReduction ) ).run( proof )
}

object AcnfReduction extends CutReduction {
  /**
    * This algorithm implements a generalization of the Gentzen method which
    * reduces all cuts to atomic cuts.
    *
    * @param proof            The proof to subject to cut-elimination.
    * @return The cut-free proof.
    */
  def reduce( proof: CutRule ): Option[LKProof] = proof match {
    case cut @ CutRule( lsb, l, rsb, _ ) if !isAtom( lsb.endSequent( l ) ) && isAcnf( lsb ) && isAcnf( rsb ) =>
      if ( isAtom( lsb.endSequent( l ) ) )
        ( leftRankReduction orElse rightRankReduction ).reduce( cut )
      else
        ( gradeReduction orElse leftRankReduction orElse rightRankReduction ).reduce( cut )
    case _ => None
  }
}

object isAcnf {
  /**
    * This method checks whether a proof is in ACNF
    *
    * @param proof The proof to check for in ACNF.
    * @return True if proof is in ACNF, False otherwise.
    */
  def apply( proof: LKProof ): Boolean = proof match {
    case InitialSequent( _ ) => true
    case CutRule( lsb, l, rsb, r ) =>
      if ( isAtom( lsb.endSequent( l ) ) ) isAcnf( lsb ) && isAcnf( rsb )
      else false
    case _ => proof.immediateSubProofs.forall( isAcnf( _ ) )
  }
}

object acnfTop {
  def apply(proof: LKProof) =
    (new UppermostFirstStrategy( AcnfTopReduction ) ).run( proof )
}

object AcnfTopReduction extends CutReduction {

  import at.logic.gapt.expr.hol.isAtom

  def reduce( proof: CutRule ): Option[LKProof] =
    proof match {
      case cut @ CutRule( lsb, l, rsb, r ) if isAtomicCut( cut ) =>
        if ( !( introOrCut( lsb, lsb.endSequent( l ) ) && introOrCut( rsb, rsb.endSequent( r ) ) ) ) {
          if ( introOrCut( lsb, lsb.endSequent( l ) ) )
            rightRankReduction.reduce( cut )
          else
            ( leftRankReduction orElse rightRankReduction ).reduce( cut )
        } else {
          None
        }
      case cut @ CutRule( lsb, _, rsb, _ ) if isAcnfTop( lsb ) && isAcnfTop( rsb ) =>
        ( gradeReduction orElse leftRankReduction orElse rightRankReduction ).reduce( cut )
      case _ => None
    }
}

object isAcnfTop {
  /**
    * This method checks whether a proof is in ACNF top
    *
    * @param proof The proof to check for in ACNF top.
    * @return True if proof is in ACNF,  False otherwise.
    */
  def apply( proof: LKProof ): Boolean = proof match {
    case InitialSequent( _ ) => true
    case CutRule( lsb, l, rsb, r ) =>
      if ( isAtom( lsb.endSequent( l ) ) )
        if ( introOrCut( lsb, lsb.endSequent( l ) ) && introOrCut( rsb, rsb.endSequent( r ) ) )
          isAcnfTop( lsb ) && isAcnfTop( rsb )
        else false
      else false
    case _ => proof.immediateSubProofs.forall( isAcnfTop( _ ) )
  }
}

object isAtomicCut {
  def apply(cut: CutRule ): Boolean = isAtom( cut.cutFormula )
}

object introOrCut {
  /**
    * Checks if the last rule in proof is a leaf, a cut rule, or a weakening rule on
    * the given formula.
    *
    * @param proof   The proof we are checking.
    * @param formula The formula we are checking.
    * @return True is structure is correct or false if not.
    */
  def apply( proof: LKProof, formula: Formula ): Boolean = proof match {
    case LogicalAxiom( _ )             => true
    case CutRule( lsb, l, rsb, r )     => true
    case WeakeningRightRule( _, main ) => if ( main == formula ) true else false
    case WeakeningLeftRule( _, main )  => if ( main == formula ) true else false
    case _                             => false
  }
}