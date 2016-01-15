package at.logic.gapt.expr.fol

import at.logic.gapt.expr._
import at.logic.gapt.proofs.HOLSequent

/**
 * The interface for an unification algorithm of finitary type, i.e.
 * one where the complete set of most general unifiers is finite.
 */
trait FinitaryUnification {
  /**
   * Calculates the complete set of most general unifiers of the terms term1 and term2.
   * @param term1 one of the terms to unify. formulas are also allowed, so we accept FOL expressions
   * @param term2 one of the terms to unify. formulas are also allowed, so we accept FOL expressions
   * @return a list of mgus, the empty list means that term1 and term2 are not unifiable.
   */
  def unify( term1: FOLExpression, term2: FOLExpression ): List[FOLSubstitution]
}

trait UnificationAlgorithm extends FinitaryUnification

class UnificationException( msg: String ) extends Exception( msg )

/**
 * Created by sebastian on 2/9/15.
 */
object FOLUnificationAlgorithm extends UnificationAlgorithm {

  //  def unify( seq1: HOLSequent, seq2: HOLSequent ): List[FOLSubstitution] = syntacticMGU(seq1.toFormula.asInstanceOf[FOLFormula], seq2.toFormula.asInstanceOf[FOLFormula]).toList

  def unify( term1: FOLExpression, term2: FOLExpression ): List[FOLSubstitution] = syntacticMGU( term1, term2 ).toList
}
