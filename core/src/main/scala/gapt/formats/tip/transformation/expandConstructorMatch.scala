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
import gapt.formats.tip.parser.TipSmtOr
import gapt.formats.tip.parser.TipSmtProblem
import gapt.formats.tip.util.TipSubstitute

object expandConstructorMatch extends TipSmtProblemTransformation {

  /**
   * Expands constructor match-expressions in the given problem.
   *
   * @return A problem whose expressions do not contain any constructor
   * match-expressions.
   */
  def transform( problem: TipSmtProblem ): TipSmtProblem =
    new ExpandConstructorMatch( problem )()
}

/**
 * Expands constructor match-expressions.
 *
 * A constructor match expression is an expression of the form
 *
 * ( match (c_i t_1 ... t_{n_i})
 *   ( case (c_1 x_1 ... x_{n_1} e_1)
 *   ...
 *   ( case (c_k x_k ... x_{n_k} e_k)))
 *
 * with 1 <= i <= k. A constructor match-expression can be simplified into
 * the following expression
 *
 * e_i[x_1/t_1, ... x_{n_i}/t_{n_i}].
 *
 * This class expands constructor match-expressions to expression in the
 * problem. Constructor match-expressions are expanded from the outside to
 * the inside of the given expression.
 *
 * @param problem The problem whose expressions are subject to the
 * transformation.
 */
class ExpandConstructorMatch( val problem: TipSmtProblem ) {

  problem.symbolTable = Some( SymbolTable( problem ) )

  private val constructorSymbols: Set[String] =
    problem.symbolTable.get.constructors

  /**
   * Expands constructor match-expressions in the given problem.
   *
   * @return A problem whose expressions do not contain any constructor
   * match-expressions.
   */
  def apply(): TipSmtProblem = problem.copy( definitions =
    problem.definitions map {
      expandConstructorMatchDefinitionVisitor.dispatch( _, () )
    } )

  private object expandConstructorMatchDefinitionVisitor
    extends TipSmtDefinitionTransformation[Unit] {

    override def visit(
      functionDefinition: TipSmtFunctionDefinition,
      data:               Unit ): TipSmtFunctionDefinition =
      functionDefinition.copy(
        body = expandConstructorMatch( functionDefinition.body ) )

    override def visit(
      assertion: TipSmtAssertion,
      data:      Unit ): TipSmtAssertion =
      assertion.copy( expr = expandConstructorMatch( assertion.expr ) )

    override def visit(
      goal: TipSmtGoal,
      data: Unit ): TipSmtGoal =
      goal.copy( expr = expandConstructorMatch( goal.expr ) )

    override def visit(
      functionDefinitions: TipSmtMutualRecursiveFunctionDefinition,
      data:                Unit ): TipSmtMutualRecursiveFunctionDefinition =
      functionDefinitions.copy( functions = functionDefinitions.functions map {
        visit( _, data )
      } )
  }

  /**
   * Expands constructor match-expressions.
   *
   * @param expression The expression in which the constructor
   * match-expressions are to be expanded.
   * @return An expression not containing constructor match-expressions.
   */
  private def expandConstructorMatch(
    expression: TipSmtExpression ): TipSmtExpression = {
    expression match {
      case e @ TipSmtAnd( _ ) =>
        expandConstructorMatch( e )
      case e @ TipSmtOr( _ ) =>
        expandConstructorMatch( e )
      case e @ TipSmtImp( _ ) =>
        expandConstructorMatch( e )
      case e @ TipSmtEq( _ ) =>
        expandConstructorMatch( e )
      case e @ TipSmtForall( _, _ ) =>
        expandConstructorMatch( e )
      case e @ TipSmtExists( _, _ ) =>
        expandConstructorMatch( e )
      case e @ TipSmtMatch( _, _ ) =>
        expandConstructorMatch( e )
      case e @ TipSmtIte( _, _, _ ) =>
        expandConstructorMatch( e )
      case e @ TipSmtFun( _, _ ) =>
        expandConstructorMatch( e )
      case _ => expression
    }
  }

  /**
   * Expands constructor match-expressions.
   *
   * @param matchExpression The expression in which the constructor
   * match-expressions are to be expanded.
   * @return An expression not containing constructor match-expressions.
   */
  private def expandConstructorMatch(
    matchExpression: TipSmtMatch ): TipSmtExpression =
    matchExpression.expr match {
      case TipSmtFun( identifier, expressions ) if isConstructor( identifier ) =>
        val cas = retrieveCase( matchExpression, identifier )
        val TipSmtConstructorPattern( _, variables ) = cas.pattern
        val substitution = Map( variables zip expressions: _* )
        val newExpression = new TipSubstitute( problem )( cas.expr, substitution )
        expandConstructorMatch( newExpression )
      case id @ TipSmtIdentifier( _ ) if isConstructor( id ) =>
        expandConstructorMatch( retrieveCase( matchExpression, id ).expr )
      case _ =>
        matchExpression.copy(
          cases = matchExpression.cases map { expandConstructorMatch } )
    }

  /**
   * Expands constructor match-expressions.
   *
   * @param expr The case statement whose expression is to be subject to the
   * constructor match-expression transformation.
   * @return A case statement with the same pattern whose expression does not
   * contain constructor match-expressions.
   */
  private def expandConstructorMatch(
    expr: TipSmtCase ): TipSmtCase = {
    expr.copy( expr = expandConstructorMatch( expr.expr ) )
  }

  /**
   * Expands constructor match-expressions.
   *
   * @param expr The expression in which the constructor match-expressions are
   * to be expanded.
   * @return An expression not containing constructor match-expressions.
   */
  private def expandConstructorMatch(
    expr: TipSmtAnd ): TipSmtExpression =
    expr.copy( exprs = expr.exprs map { expandConstructorMatch } )

  /**
   * Expands constructor match-expressions.
   *
   * @param expr The expression in which the constructor match-expressions are
   * to be expanded.
   * @return An expression not containing constructor match-expressions.
   */
  private def expandConstructorMatch(
    expr: TipSmtOr ): TipSmtExpression =
    expr.copy( exprs = expr.exprs map { expandConstructorMatch } )

  /**
   * Expands constructor match-expressions.
   *
   * @param expr The expression in which the constructor match-expressions are
   * to be expanded.
   * @return An expression not containing constructor match-expressions.
   */
  private def expandConstructorMatch(
    expr: TipSmtEq ): TipSmtExpression =
    expr.copy( exprs = expr.exprs map { expandConstructorMatch } )

  /**
   * Expands constructor match-expressions.
   *
   * @param expr The expression in which the constructor match-expressions are
   * to be expanded.
   * @return An expression not containing constructor match-expressions.
   */
  private def expandConstructorMatch(
    expr: TipSmtImp ): TipSmtExpression =
    expr.copy( exprs = expr.exprs map { expandConstructorMatch } )

  /**
   * Expands constructor match-expressions.
   *
   * @param expr The expression in which the constructor match-expressions are
   * to be expanded.
   * @return An expression not containing constructor match-expressions.
   */
  private def expandConstructorMatch(
    expr: TipSmtIte ): TipSmtExpression =
    TipSmtIte(
      expandConstructorMatch( expr.cond ),
      expandConstructorMatch( expr.ifTrue ),
      expandConstructorMatch( expr.ifFalse ) )

  /**
   * Expands constructor match-expressions.
   *
   * @param expr The expression in which the constructor match-expressions are
   * to be expanded.
   * @return An expression not containing constructor match-expressions.
   */
  private def expandConstructorMatch(
    expr: TipSmtExists ): TipSmtExpression =
    expr.copy( formula = expandConstructorMatch( expr.formula ) )

  /**
   * Expands constructor match-expressions.
   *
   * @param expr The expression in which the constructor match-expressions are
   * to be expanded.
   * @return An expression not containing constructor match-expressions.
   */
  private def expandConstructorMatch(
    expr: TipSmtForall ): TipSmtExpression =
    expr.copy( formula = expandConstructorMatch( expr.formula ) )

  /**
   * Expands constructor match-expressions.
   *
   * @param expr The expression in which the constructor match-expressions are
   * to be expanded.
   * @return An expression not containing constructor match-expressions.
   */
  private def expandConstructorMatch(
    expr: TipSmtFun ): TipSmtExpression =
    expr.copy( arguments = expr.arguments map { expandConstructorMatch } )

  /**
   * Retrieves a case-statement of a given match-expression.
   *
   * @param matchExpression The match-expression for which the case-statement
   * is to be retrieved.
   * @param constructor The constructor whose corresponding case-statement is
   * to be retrieved.
   * @return The case-statement of the given match-expression whose pattern is
   * based on the given constructor symbol.
   */
  private def retrieveCase(
    matchExpression: TipSmtMatch, constructor: TipSmtIdentifier ): TipSmtCase =
    retrieveCase( matchExpression, constructor.name )

  /**
   * Retrieves a case-statement of a given match-expression.
   *
   * @param matchExpression The match-expression for which the case-statement
   * is to be retrieved.
   * @param constructor The constructor whose corresponding case-statement is
   * to be retrieved.
   * @return The case-statement of the given match-expression whose pattern is
   * based on the given constructor symbol.
   */
  private def retrieveCase(
    matchExpression: TipSmtMatch, constructor: String ): TipSmtCase =
    matchExpression.cases.filter {
      case TipSmtCase( TipSmtConstructorPattern( TipSmtIdentifier( symbol ), _ ), _ ) if constructor == symbol => true
      case _ => false
    } head

  /**
   * Checks whether the given identifier is a constructor.
   *
   * @param symbol The identifier to be checked.
   * @return true if the given identifier is a constructor, false otherwise.
   */
  private def isConstructor( symbol: TipSmtIdentifier ): Boolean =
    isConstructor( symbol.name )

  /**
   * Checks whether the given string is constructor symbol.
   *
   * @param symbol The symbol to be checked.
   * @return true if the given symbol is the name of a constructor, false
   * otherwise.
   */
  private def isConstructor( symbol: String ): Boolean =
    constructorSymbols.contains( symbol )
}
