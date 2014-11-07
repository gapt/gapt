package at.logic.provers

import at.logic.language.hol.HOLFormula
import at.logic.calculi.lk.base._

/**
  A prover that is able to refute HOL sequents/formulas (or subsets
  of HOL, like propositional logic).

  TODO: exceptions to indicate that a formula is not supported (e.g.
  for propositional provers).

  Implementors may want to override isValid(seq) to avoid parsing 
  proofs.
**/

trait Prover {
  /**
    @param formula The formula whose validity should be checked.
    @return True if the formula is valid.
  **/
  def isValid( formula : HOLFormula ) : Boolean = isValid( FSequent( Nil, formula::Nil ) )

  /**
    @param seq The formula whose validity should be checked.
    @return True if the formula is valid.
  **/
  def isValid( seq : FSequent ) : Boolean = getLKProof( seq ) match {
    case Some(_) => true
    case None => false
  }

  /**
    @param formula The formula that should be proved.
    @return An LK-Proof of  :- formula, or None if not successful.
  **/
  def getLKProof( formula : HOLFormula ) : Option[LKProof] = getLKProof( FSequent( Nil, formula::Nil ) )

  /**
    @param seq The sequent that should be proved.
    @return An LK-Proof of the sequent, or None if not successful.
  **/
  def getLKProof( seq : FSequent ) : Option[LKProof]
}
