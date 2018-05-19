package gapt.formats.tip.transformation

import gapt.formats.tip.parser.TipSmtAnd
import gapt.formats.tip.parser.TipSmtAssertion
import gapt.formats.tip.parser.TipSmtEq
import gapt.formats.tip.parser.TipSmtExists
import gapt.formats.tip.parser.TipSmtExpression
import gapt.formats.tip.parser.TipSmtFalse
import gapt.formats.tip.parser.TipSmtForall
import gapt.formats.tip.parser.TipSmtFun
import gapt.formats.tip.parser.TipSmtFunctionDefinition
import gapt.formats.tip.parser.TipSmtGoal
import gapt.formats.tip.parser.TipSmtImp
import gapt.formats.tip.parser.TipSmtIte
import gapt.formats.tip.parser.TipSmtMatch
import gapt.formats.tip.parser.TipSmtNot
import gapt.formats.tip.parser.TipSmtOr
import gapt.formats.tip.parser.TipSmtProblem
import gapt.formats.tip.parser.TipSmtTrue

class BooleanConstantElimination( problem: TipSmtProblem ) {

  /**
   * Eliminates boolean constants in the given tip problem.
   *
   * This eliminates boolean constants in function definitions, goals and
   * assertions.
   *
   * @return A tip problem.
   */
  def apply(): TipSmtProblem = {
    problem.copy( definitions = problem.definitions map {
      case goal @ TipSmtGoal( _, formula ) =>
        goal.copy( expr = eliminateBooleanConstants( formula ) )
      case assertion @ TipSmtAssertion( _, formula ) =>
        assertion.copy( expr = eliminateBooleanConstants( formula ) )
      case fun @ TipSmtFunctionDefinition( _, _, _, _, body ) =>
        fun.copy( body = eliminateBooleanConstants( body ) )
      case definition => definition
    } )
  }

  /**
    * Eliminates boolean constants in the given expression.
    *
    * @param expression The expression in which the boolean constants are to be
    *                   eliminated. This expression must only contain symbols of
    *                   the given tip problem.
    * @return A tip expression.
    */
  private def eliminateBooleanConstants(
    expression: TipSmtExpression ): TipSmtExpression = {
    expression match {
      case expr @ TipSmtAnd( _ )       => eliminateBooleanConstants( expr )
      case expr @ TipSmtOr( _ )        => eliminateBooleanConstants( expr )
      case expr @ TipSmtImp( _ )       => eliminateBooleanConstants( expr )
      case expr @ TipSmtForall( _, _ ) => eliminateBooleanConstants( expr )
      case expr @ TipSmtExists( _, _ ) => eliminateBooleanConstants( expr )
      case expr @ TipSmtIte( _, _, _ ) => eliminateBooleanConstants( expr )
      case expr @ TipSmtEq( _ )        => expr
      case expr @ TipSmtFun( _, _ )    => expr
      case expr @ TipSmtNot( _ )       => eliminateBooleanConstants( expr )
      case expr @ TipSmtMatch( _, _ )  => eliminateBooleanConstants( expr )
      case formula                     => formula
    }
  }

  /**
    * Eliminates boolean constants in the given match-expression.
    *
    * @param smtMatch The expression in which the boolean constants are to be
    *                 eliminated.
    * @return A match-expression whose matched-expression and case statements
    *         do not contain redundant boolean constants.
    */
  private def eliminateBooleanConstants(
    smtMatch: TipSmtMatch ): TipSmtExpression = {
    smtMatch.copy( cases = smtMatch.cases.map { c =>
      c.copy( expr = eliminateBooleanConstants( c.expr ) )
    } )
  }

  /**
    * Eliminates boolean constants in the given not-expression.
    *
    * @param not The expression in which the boolean constants are to be
    *            eliminated.
    * @return An expression without redundant boolean constants.
    */
  private def eliminateBooleanConstants( not: TipSmtNot ): TipSmtExpression = {
    eliminateBooleanConstants( not.expr ) match {
      case TipSmtFalse => TipSmtTrue
      case TipSmtTrue  => TipSmtFalse
      case formula     => TipSmtNot( formula )
    }
  }

  /**
    * Eliminates boolean constants in the given and-expression.
    *
    * @param and The expression in which the boolean constants are to be
    *            eliminated.
    * @return An expression without redundant boolean constants.
    */
  private def eliminateBooleanConstants( and: TipSmtAnd ): TipSmtExpression = {
    val remainingExpressions = and.exprs
      .map { eliminateBooleanConstants }
      .filter { _ != TipSmtTrue }
    if ( remainingExpressions.contains( TipSmtFalse ) ) {
      TipSmtFalse
    } else if ( remainingExpressions.isEmpty ) {
      TipSmtTrue
    } else {
      TipSmtAnd( remainingExpressions )
    }
  }

  /**
    * Eliminates boolean constants in the given or-expression.
    *
    * @param or The expression in which the boolean constants are to be
    *           eliminated.
    * @return An expression without redundant boolean constants.
    */
  private def eliminateBooleanConstants( or: TipSmtOr ): TipSmtExpression = {
    val remainingExpressions = or.exprs
      .map { eliminateBooleanConstants }
      .filter { _ != TipSmtFalse }
    if ( remainingExpressions.contains( TipSmtTrue ) ) {
      TipSmtTrue
    } else if ( remainingExpressions.isEmpty ) {
      TipSmtFalse
    } else {
      TipSmtOr( remainingExpressions )
    }
  }

  /**
    * Eliminates boolean constants in the given imp-expression.
    *
    * @param imp The expression in which the boolean constants are to be
    *            eliminated.
    * @return An expression without redundant boolean constants.
    */
  private def eliminateBooleanConstants( imp: TipSmtImp ): TipSmtExpression = {
    val newExpressions = imp.exprs map { eliminateBooleanConstants }
    val finalExpressions =
      newExpressions.init.foldRight( Seq( newExpressions.last ) ) {
        case ( _, Seq( TipSmtTrue ) ) =>
          Seq( TipSmtTrue )
        case ( l, Seq( TipSmtFalse ) ) =>
          Seq( eliminateBooleanConstants( TipSmtNot( l ) ) )
        case ( TipSmtTrue, r ) =>
          r
        case ( TipSmtFalse, _ ) =>
          Seq( TipSmtTrue )
        case ( l, r ) =>
          l +: r
      }
    finalExpressions match {
      case Seq( formula ) => formula
      case _              => TipSmtImp( finalExpressions )
    }
  }

  /**
    * Eliminates boolean constants in the given forall-expression.
    *
    * @param forall The expression in which the boolean constants are to be
    *               eliminated.
    * @return An expression without redundant boolean constants.
    */
  private def eliminateBooleanConstants(
    forall: TipSmtForall ): TipSmtExpression = {
    eliminateBooleanConstants( forall.formula ) match {
      case TipSmtTrue  => TipSmtTrue
      case TipSmtFalse => TipSmtFalse
      case expression  => TipSmtForall( forall.variables, expression )
    }
  }

  /**
    * Eliminates boolean constants in the given exists-expression.
    *
    * @param exists The expression in which the boolean constants are to be
    *               eliminated.
    * @return An expression without redundant boolean constants.
    */
  private def eliminateBooleanConstants(
    exists: TipSmtExists ): TipSmtExpression = {
    eliminateBooleanConstants( exists.formula ) match {
      case TipSmtTrue  => TipSmtTrue
      case TipSmtFalse => TipSmtFalse
      case expression  => TipSmtExists( exists.variables, expression )
    }
  }

  /**
    * Eliminates boolean constants in the given ite-expression.
    *
    * @param ite The expression in which the boolean constants are to be
    *            eliminated.
    * @return An expression without redundant boolean constants.
    */
  private def eliminateBooleanConstants(
    ite: TipSmtIte ): TipSmtExpression = {
    eliminateBooleanConstants( ite.cond ) match {
      case TipSmtTrue  => eliminateBooleanConstants( ite.the )
      case TipSmtFalse => eliminateBooleanConstants( ite.els )
      case newCond => TipSmtIte(
        newCond,
        eliminateBooleanConstants( ite.the ),
        eliminateBooleanConstants( ite.els ) )
    }
  }
}
