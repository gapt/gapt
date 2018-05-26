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

object expandVariableMatchExpressions extends TipSmtProblemTransformation {
  override def transform( problem: TipSmtProblem ): TipSmtProblem =
    new VariableMatchExpansion( problem )()
}

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

  private sealed trait Polarity
  private case object Forall extends Polarity
  private case object Exists extends Polarity

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
          goal.copy( expr =
            expandVariableMatch( formula, Map[String, Polarity]() ) )
        case assertion @ TipSmtAssertion( _, formula ) =>
          assertion.copy( expr =
            expandVariableMatch( formula, Map[String, Polarity]() ) )
        case definition => definition
      }
    } )
  }

  private def apply(
    fun: TipSmtFunctionDefinition ): TipSmtFunctionDefinition = {
    fun.copy( body = expandVariableMatch( fun.body, Map[String, Polarity]() ) )
  }

  /**
   * Expands variable-match expressions in the given expression.
   *
   * @param expression The expression whose variable-match expressions are to
   *                   be expanded.
   * @return An expression without variable-match subexpressions.
   */
  def expandVariableMatch(
    expression: TipSmtExpression,
    variables:  Map[String, Polarity] ): TipSmtExpression = {
    expression match {
      case expr @ TipSmtAnd( _ ) =>
        expr.copy( expr.exprs.map { expandVariableMatch( _, variables ) } )
      case expr @ TipSmtOr( _ ) =>
        expr.copy( expr.exprs.map { expandVariableMatch( _, variables ) } )
      case expr @ TipSmtImp( _ ) =>
        expr.copy( expr.exprs.map { expandVariableMatch( _, variables ) } )
      case expr @ TipSmtEq( _ ) =>
        expr.copy( expr.exprs.map { expandVariableMatch( _, variables ) } )
      case expr @ TipSmtFun( _, _ ) =>
        expr.copy( arguments =
          expr.arguments.map { expandVariableMatch( _, variables ) } )
      case expr @ TipSmtNot( _ ) =>
        expr.copy( expandVariableMatch( expr.expr, variables ) )
      case expr @ TipSmtForall( _, _ ) =>
        expandVariableMatch( expr, variables )
      case expr @ TipSmtExists( _, _ ) =>
        expandVariableMatch( expr, variables )
      case expr @ TipSmtMatch( _, _ ) =>
        expandVariableMatch( expr, variables )
      case expr @ TipSmtIte( _, _, _ ) =>
        TipSmtIte(
          expandVariableMatch( expr.cond, variables ),
          expandVariableMatch( expr.ifTrue, variables ),
          expandVariableMatch( expr.ifFalse, variables ) )
      case _ => expression
    }
  }

  private def expandVariableMatch(
    forall:    TipSmtForall,
    variables: Map[String, Polarity] ): TipSmtExpression = {
    val newVariables = variables ++ forall.variables.map { _.name -> Forall }
    forall.copy( formula = expandVariableMatch( forall.formula, newVariables ) )
  }

  private def expandVariableMatch(
    exists:    TipSmtExists,
    variables: Map[String, Polarity] ): TipSmtExpression = {
    val newVariables = variables ++ exists.variables.map { _.name -> Exists }
    exists.copy( formula = expandVariableMatch( exists.formula, newVariables ) )
  }

  /**
   * Expands variable-match expressions in the given expression.
   *
   * @param tipSmtMatch The expression whose variable-match expressions are to
   *                    be expanded.
   * @return An expression without variable-match subexpressions.
   */
  def expandVariableMatch(
    tipSmtMatch: TipSmtMatch,
    variables:   Map[String, Polarity] ): TipSmtExpression = {
    tipSmtMatch.expr match {
      case identifier @ TipSmtIdentifier( _ ) //
      if variables.contains( identifier.name ) =>
        val polarity = variables( identifier.name )
        val connective = polarity match {
          case Forall => TipSmtAnd
          case Exists => TipSmtOr
        }
        connective( tipSmtMatch.cases
          .map { expandCaseStatement( identifier, _, polarity ) }
          .map { expandVariableMatch( _, variables ) } )

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
    tipSmtCase: TipSmtCase,
    polarity:   Polarity ): TipSmtExpression = {
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
    val quantifier = polarity match {
      case Forall => TipSmtForall
      case Exists => TipSmtExists
    }
    quantifier(
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
    tipSmtCase.copy(
      expr = expandVariableMatch( tipSmtCase.expr, Map[String, Polarity]() ) )

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
