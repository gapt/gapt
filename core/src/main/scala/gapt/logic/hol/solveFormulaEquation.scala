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
import gapt.logic.hol.dls.dls
import gapt.provers.escargot.Escargot

import scala.util.Failure
import scala.util.Success
import scala.util.Try
import gapt.expr.formula.hol.freeHOVariables.isHOVar

/**
 * Takes a formula equation F[X₁,...,Xₙ] and if successful returns a substitution of the second order
 * variables X_1,...,X_n such that applying the substitution to F is a valid first-order formula.
 * See [[dls]] for a detailed description when this succeeds and when it fails.
 * In addition, this method uses Escargot to check if the found first-order formula is valid and returns a Failure,
 * if it is not.
 */
object solveFormulaEquation {

  /**
   * Attempts to solve formula equations.
   * @param f The formula equation `F[X₁,...,Xₙ]` in form of a predicate elimination problem.
   */
  def apply(input: PredicateEliminationProblem): Try[Substitution] = {
    dls(input).flatMap({
      case (substitution, firstOrderPart) =>
        if (Escargot.isValid(BetaReduction.betaNormalize(substitution(firstOrderPart))))
          Success(substitution)
        else
          Failure(new Exception(s"""the given formula equation ${input} is not solvable"""))
    })
  }
}
