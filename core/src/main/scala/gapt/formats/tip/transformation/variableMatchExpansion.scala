package gapt.formats.tip.transformation

import gapt.formats.tip.analysis.SymbolTable
import gapt.formats.tip.parser.TipSmtAnd
import gapt.formats.tip.parser.TipSmtAssertion
import gapt.formats.tip.parser.TipSmtCase
import gapt.formats.tip.parser.TipSmtConstructorPattern
import gapt.formats.tip.parser.TipSmtEq
import gapt.formats.tip.parser.TipSmtExists
import gapt.formats.tip.parser.TipSmtExpression
import gapt.formats.tip.parser.TipSmtForall
import gapt.formats.tip.parser.TipSmtFun
import gapt.formats.tip.parser.TipSmtFunctionDefinition
import gapt.formats.tip.parser.TipSmtGoal
import gapt.formats.tip.parser.TipSmtIdentifier
import gapt.formats.tip.parser.TipSmtImp
import gapt.formats.tip.parser.TipSmtIte
import gapt.formats.tip.parser.TipSmtMatch
import gapt.formats.tip.parser.TipSmtMutualRecursiveFunctionDefinition
import gapt.formats.tip.parser.TipSmtNot
import gapt.formats.tip.parser.TipSmtOr
import gapt.formats.tip.parser.TipSmtProblem
import gapt.formats.tip.parser.TipSmtType
import gapt.formats.tip.parser.TipSmtVariableDecl
import gapt.formats.tip.util.TipSubstitute

/**
 * This class expands Boolean match-expressions whose matched expression is
 * a variable.
 *
 * Let E be the boolean match-expression
 *     ( match x ( case p_1 e_1) ... (case p_n e_n)),
 * and let X_i be the variables in pattern p_i. Then the expression E is
 * expanded into the formula
 *     !X_1 (e_1[x/p_1]) & ... & !X_n (e_n[x/p_n]).
 *
 * The variable-match-expressions are expanded from outside to inside.
 *
 * @param problem A well-formed TIP problem whose variable-match expressions
 *                are to be expanded.
 */
class VariableMatchExpansion( problem: TipSmtProblem ) {

  problem.symbolTable = Some( SymbolTable( problem ) )

  /**
   * Expands variable-match expressions in the given problem.
   *
   * Variable-match expressions are expanded in function definitions, goals and
   * assertions.
   *
   * @return A problem without variable-match expressions.
   */
  def apply(): TipSmtProblem = {
    problem.copy( definitions = problem.definitions map {
      _ match {
        case fun @ TipSmtFunctionDefinition( _, _, _, _, body ) =>
          apply( fun )
        case funDefs @ TipSmtMutualRecursiveFunctionDefinition( _ ) =>
          funDefs.copy( functions = funDefs.functions.map { apply } )
        case goal @ TipSmtGoal( _, formula ) =>
          goal.copy( expr = expandVariableMatch( formula ) )
        case assertion @ TipSmtAssertion( _, formula ) =>
          assertion.copy( expr = expandVariableMatch( formula ) )
        case definition => definition
      }
    } )
  }

  private def apply(
    fun: TipSmtFunctionDefinition ): TipSmtFunctionDefinition = {
    fun.copy( body = expandVariableMatch( fun.body ) )
  }

  /**
   * Expands variable-match expressions in the given expression.
   *
   * @param expression The expression whose variable-match expressions are to
   *                   be expanded.
   * @return An expression without variable-match subexpressions.
   */
  def expandVariableMatch( expression: TipSmtExpression ): TipSmtExpression = {
    expression match {
      case expr @ TipSmtAnd( _ ) =>
        expr.copy( expr.exprs.map { expandVariableMatch } )
      case expr @ TipSmtOr( _ ) =>
        expr.copy( expr.exprs.map { expandVariableMatch } )
      case expr @ TipSmtImp( _ ) =>
        expr.copy( expr.exprs.map { expandVariableMatch } )
      case expr @ TipSmtEq( _ ) =>
        expr.copy( expr.exprs.map { expandVariableMatch } )
      case expr @ TipSmtFun( _, _ ) =>
        expr.copy( arguments = expr.arguments.map { expandVariableMatch } )
      case expr @ TipSmtNot( _ ) =>
        expr.copy( expandVariableMatch( expr.expr ) )
      case expr @ TipSmtForall( _, _ ) =>
        expr.copy( formula = expandVariableMatch( expr.formula ) )
      case expr @ TipSmtExists( _, _ ) =>
        expr.copy( formula = expandVariableMatch( expr.formula ) )
      case expr @ TipSmtMatch( _, _ ) =>
        expandVariableMatch( expr )
      case expr @ TipSmtIte( _, _, _ ) =>
        TipSmtIte(
          expandVariableMatch( expr.cond ),
          expandVariableMatch( expr.the ),
          expandVariableMatch( expr.els ) )
      case _ => expression
    }
  }

  /**
   * Expands variable-match expressions in the given expression.
   *
   * @param tipSmtMatch The expression whose variable-match expressions are to
   *                    be expanded.
   * @return An expression without variable-match subexpressions.
   */
  def expandVariableMatch( tipSmtMatch: TipSmtMatch ): TipSmtExpression = {
    tipSmtMatch.expr match {
      case identifier @ TipSmtIdentifier( _ ) if isVariable( identifier ) =>
        TipSmtAnd( tipSmtMatch.cases
          .map { expandCaseStatement( identifier, _ ) }
          .map { expandVariableMatch } )
      case _ => tipSmtMatch.copy( cases = tipSmtMatch.cases map {
        expandVariableMatch
      } )
    }
  }

  /**
   * Converts a case statement of a variable-match expression into a formula.
   *
   * @param variable The variable that is matched upon.
   * @param tipSmtCase The case statement to be expanded.
   * @return A formula of the form !X (e[x/p]), where X are the
   *         variables occurring in the case-statement's pattern, e is the case
   *         statement's expression and p is the case statement's pattern.
   */
  def expandCaseStatement(
    variable:   TipSmtIdentifier,
    tipSmtCase: TipSmtCase ): TipSmtExpression = {
    val pattern @ TipSmtConstructorPattern( _, _ ) = tipSmtCase.pattern
    val boundVariables =
      problem
        .symbolTable.get.typeOf( pattern.constructor.name )
        .argumentTypes.zip( pattern.identifiers )
        .filter { case ( _, field ) => isVariable( field ) }
        .map {
          case ( ty, field ) =>
            TipSmtVariableDecl( field.name, TipSmtType( ty.name ) )
        }
    TipSmtForall(
      boundVariables,
      ( new TipSubstitute( problem ) )(
        tipSmtCase.expr,
        variable.name,
        patternToExpression( pattern ) ) )
  }

  /**
   * Converts a pattern into an expression.
   *
   * @param pattern The pattern to be converted into an expression.
   * @return A formula representing the pattern.
   */
  def patternToExpression(
    pattern: TipSmtConstructorPattern ): TipSmtExpression = {
    TipSmtFun( pattern.constructor.name, pattern.identifiers )
  }

  /**
   * Expands variable-match expressions in the given case-statement.
   * @param tipSmtCase The case statement in whose expression variable-match
   *                   expressions are expanded.
   * @return A case statement whose expression does not contain variable
   *         patterns.
   */
  def expandVariableMatch( tipSmtCase: TipSmtCase ): TipSmtCase =
    tipSmtCase.copy( expr = expandVariableMatch( tipSmtCase.expr ) )

  /**
   * Checks whether the given identifier represents a variable.
   *
   * @param identifier The identifier to be checked.
   * @return true if the given identifier is a variable, false otherwise.
   */
  def isVariable( identifier: TipSmtIdentifier ): Boolean = {
    !problem.symbolTable.get.contains( identifier.name )
  }
}
