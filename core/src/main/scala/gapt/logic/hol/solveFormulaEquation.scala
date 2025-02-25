package gapt.logic.hol

import gapt.expr.BetaReduction
import gapt.expr.Var
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.subst.Substitution
import gapt.expr.ty.FunctionType
import gapt.expr.ty.To
import gapt.expr.ty.Ty
import gapt.expr.util.freeVariables
import gapt.logic.hol.wdls.wdls
import gapt.provers.escargot.Escargot

import scala.util.Failure
import scala.util.Success
import scala.util.Try
import gapt.expr.formula.hol.freeHOVariables.isHOVar

/**
 * Takes a predicate elimination problem  ∃X₁ ... ∃Xₙ φ and if successful returns a substitution of the second order
 * variables X₁,...,Xₙ such that applying the substitution to φ is a valid first-order formula.
 * The method uses [[wdls]] to construct a substitution such that applying it to φ gives a formula equivalent to ∃X₁ ... ∃Xₙ φ.
 * Then Escargot is used to check if the found first-order formula is valid and returns a Failure, if it is not.
 * 
 * See [[wdls]] for a detailed description when this succeeds and when it fails.
 */
object solveFormulaEquation {

  /**
   * Attempts to solve formula equations.
   * @param f The formula equation ∃X₁ ... ∃Xₙ φ in form of a predicate elimination problem.
   */
  def apply(input: PredicateEliminationProblem): Try[Substitution] = {
    wdls(input).flatMap({
      case substitution =>
        if (Escargot.isValid(BetaReduction.betaNormalize(substitution(input.firstOrderPart))))
          Success(substitution)
        else
          Failure(new Exception(s"""the given formula equation ${input} is not solvable"""))
    })
  }
}
