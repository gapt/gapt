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
import gapt.provers.escargot.Escargot

import scala.util.Failure
import scala.util.Success
import scala.util.Try

/**
 * Takes a formula equation F[X₁,...,Xₙ] and if successful returns a substitution of the second order
 * variables X_1,...,X_n such that applying the substitution to F is a valid first-order formula.
 * See [[dls]] for a detailed description when this succeeds and when it fails.
 * In addition, this method uses Escargot to check if the found first-order formula is valid and returns a Failure,
 * if it is not.
 */
object solveFormulaEquation {

  private def isHigherOrderPredicateType( t: Ty ) =
    t match {
      case FunctionType( To, _ ) => true
      case _                     => false
    }

  private def isHigherOrderPredicateVariable( x: Var ) =
    isHigherOrderPredicateType( x.ty )

  /**
   * Attempts to solve formula equations.
   * @param f The formula equation `F[X₁,...,Xₙ]` to be solved.
   */
  def apply( f: Formula ): Try[Substitution] = {
    val xs = freeVariables( f ).filter( isHigherOrderPredicateVariable ).toSeq
    val h = Ex.Block( xs, f )
    dls( h ).flatMap( {
      case ( substitution, firstOrderPart ) =>
        if ( Escargot.isValid( BetaReduction.betaNormalize( substitution( firstOrderPart ) ) ) )
          Success( substitution )
        else
          Failure( new Exception( s"""the given formula equation ${f} is not solvable""" ) )
    } )
  }
}
