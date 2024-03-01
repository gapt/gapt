package gapt.formats.tip.transformation

import gapt.formats.tip.analysis.retrieveDatatypes
import gapt.formats.tip.decoration.ReconstructDatatypes
import gapt.formats.tip.parser.TipSmtAnd
import gapt.formats.tip.parser.TipSmtAssertion
import gapt.formats.tip.parser.TipSmtCase
import gapt.formats.tip.parser.TipSmtConstructor
import gapt.formats.tip.parser.TipSmtConstructorPattern
import gapt.formats.tip.parser.TipSmtDefault
import gapt.formats.tip.parser.TipSmtDistinct
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
import gapt.utils.NameGenerator

object expandDefaultPatterns extends TipSmtProblemTransformation {
  override def transform( problem: TipSmtProblem ): TipSmtProblem =
    new TipSmtDefaultPatternExpansion( problem )()
}

/**
 * This class implements default pattern expansion for TIP problems.
 *
 * Default patterns expansion replaces default patterns by a case statement
 * for each of the constructors that are covered by the default pattern.
 *
 * @param problem The problem whose default patterns are expanded. The problem
 *               needs to be well-formed.
 */
class TipSmtDefaultPatternExpansion( problem: TipSmtProblem ) {

  ( new ReconstructDatatypes( problem ) )()

  /**
   * Expands all default patterns in the given problem. The expansion takes
   * place in the input problem.
   */
  def apply(): TipSmtProblem = {
    problem.copy( definitions = problem.definitions map {
      _ match {
        case fun @ TipSmtFunctionDefinition( _, _, _, _, _ ) =>
          apply( fun )

        case d @ TipSmtGoal( _, _ ) =>
          d.copy( expr = expandDefaultPatterns( d.expr, Seq() ) )

        case funDefs @ TipSmtMutualRecursiveFunctionDefinition( _ ) =>
          funDefs.copy( functions = funDefs.functions.map { apply } )

        case d @ TipSmtAssertion( _, _ ) =>
          d.copy( expr = expandDefaultPatterns( d.expr, Seq() ) )

        case d => d
      }
    } )
  }

  private def apply(
    fun: TipSmtFunctionDefinition ): TipSmtFunctionDefinition = {
    val context = fun.parameters map {
      _.name
    }
    fun.copy( body = expandDefaultPatterns( fun.body, context ) )
  }

  /**
   * Expands default patterns in the given expression.
   *
   * @param expr The expression in whose default patterns are expanded.
   * @param visibleVariables The variables that are visible to the given
   *                         expression
   */
  private def expandDefaultPatterns(
    expr:             TipSmtExpression,
    visibleVariables: Seq[String] ): TipSmtExpression = expr match {
    case e @ TipSmtAnd( _ ) =>
      expandDefaultPatterns( e, visibleVariables )
    case e @ TipSmtOr( _ ) =>
      expandDefaultPatterns( e, visibleVariables )
    case e @ TipSmtImp( _ ) =>
      expandDefaultPatterns( e, visibleVariables )
    case e @ TipSmtFun( _, _ ) =>
      expandDefaultPatterns( e, visibleVariables )
    case e: TipSmtForall =>
      expandDefaultPatterns( e, visibleVariables )
    case e: TipSmtExists =>
      expandDefaultPatterns( e, visibleVariables )
    case e @ TipSmtMatch( _, _ ) =>
      expandDefaultPatterns( e, visibleVariables )
    case e @ TipSmtIte( _, _, _ ) =>
      expandDefaultPatterns( e, visibleVariables )
    case e: TipSmtDistinct =>
      expandDefaultPatterns( e, visibleVariables )
    case e: TipSmtEq =>
      expandDefaultPatterns( e, visibleVariables )
    case e: TipSmtNot =>
      expandDefaultPatterns( e, visibleVariables )
    case _ => expr
  }

  private def expandDefaultPatterns(
    expression:       TipSmtNot,
    visibleVariables: Seq[String] ): TipSmtNot = {
    expression.copy( expr = expandDefaultPatterns( expression.expr, visibleVariables ) )
  }

  private def expandDefaultPatterns(
    equality:         TipSmtEq,
    visibleVariables: Seq[String] ): TipSmtEq = {
    equality.copy( exprs = equality.exprs.map { expandDefaultPatterns( _, visibleVariables ) } )
  }

  private def expandDefaultPatterns(
    distinct:         TipSmtDistinct,
    visibleVariables: Seq[String] ): TipSmtDistinct = {
    distinct.copy( expressions = distinct.expressions.map { expandDefaultPatterns( _, visibleVariables ) } )
  }

  private def expandDefaultPatterns(
    expr: TipSmtMatch, visibleVariables: Seq[String] ): TipSmtMatch = {
    val newMatchExpr =
      if ( containsDefaultPattern( expr ) ) {
        expandDefaultPattern( expr, visibleVariables )
      } else {
        expr
      }
    newMatchExpr.copy(
      expr = expandDefaultPatterns( newMatchExpr.expr, visibleVariables ),
      cases = newMatchExpr.cases.map { expandDefaultPatterns( _, visibleVariables ) } )
  }

  private def expandDefaultPatterns(
    expr: TipSmtIte, visibleVariables: Seq[String] ): TipSmtExpression = {
    TipSmtIte(
      expandDefaultPatterns( expr.cond, visibleVariables ),
      expandDefaultPatterns( expr.ifTrue, visibleVariables ),
      expandDefaultPatterns( expr.ifFalse, visibleVariables ) )
  }

  private def expandDefaultPatterns(
    expr: TipSmtExists, visibleVariables: Seq[String] ): TipSmtExpression = {
    expr.copy( formula = expandDefaultPatterns(
      expr.formula,
      visibleVariables ++ expr.variables.map( _.name ) ) )
  }

  private def expandDefaultPatterns(
    expr: TipSmtForall, visibleVariables: Seq[String] ): TipSmtExpression = {
    expr.copy( formula = expandDefaultPatterns(
      expr.formula,
      visibleVariables ++ expr.variables.map( _.name ) ) )
  }

  private def expandDefaultPatterns(
    expr: TipSmtOr, visibleVariables: Seq[String] ): TipSmtExpression = {
    expr.copy( expr.exprs map {
      expandDefaultPatterns( _, visibleVariables )
    } )
  }

  private def expandDefaultPatterns(
    expr: TipSmtAnd, visibleVariables: Seq[String] ): TipSmtExpression = {
    expr.copy( expr.exprs map {
      expandDefaultPatterns( _, visibleVariables )
    } )
  }

  private def expandDefaultPatterns(
    expr: TipSmtImp, visibleVariables: Seq[String] ): TipSmtExpression = {
    expr.copy( expr.exprs map {
      expandDefaultPatterns( _, visibleVariables )
    } )
  }

  private def expandDefaultPatterns(
    expr: TipSmtFun, visibleVariables: Seq[String] ): TipSmtExpression = {
    expr.copy( arguments = expr.arguments map {
      expandDefaultPatterns( _, visibleVariables )
    } )
  }

  /**
   * Expands default patterns in the given case statement.
   *
   * @param cas The case statement whose default patterns are expanded.
   * @param visibleVariables The variables visible to this case statement.
   */
  private def expandDefaultPatterns(
    cas:              TipSmtCase,
    visibleVariables: Seq[String] ): TipSmtCase = {
    cas.pattern match {
      case TipSmtConstructorPattern( _, fields ) =>
        val variableFields = fields
          .map { _.name }
          .filter { !problem.symbolTable.get.contains( _ ) }
        cas.copy( expr =
          expandDefaultPatterns(
            cas.expr, visibleVariables ++ variableFields ) )
      case TipSmtDefault =>
        cas.copy( expr = expandDefaultPatterns( cas.expr, visibleVariables ) )
    }
  }

  /**
   * Checks whether the given match-statement contains a default pattern.
   *
   * @param tipSmtMatch The match-expression to be checked.
   * @return true if the given match-expression contains a default pattern,
   *         false otherwise.
   */
  private def containsDefaultPattern( tipSmtMatch: TipSmtMatch ): Boolean = {
    tipSmtMatch.cases.exists { _.pattern == TipSmtDefault }
  }

  /**
   * Expands the default pattern of the given match-expression.
   *
   * @param tipSmtMatch The match-expression whose default pattern is to be
   *                    expanded.
   * @param visibleVariables The variables visible to this match-expression.
   */
  private def expandDefaultPattern(
    tipSmtMatch:      TipSmtMatch,
    visibleVariables: Seq[String] ): TipSmtMatch = {
    val TipSmtMatch( _, cases ) = tipSmtMatch
    val Some( matchedType ) = tipSmtMatch.expr.datatype: @unchecked
    val coveredConstructors: Seq[String] =
      coveredConstrs( cases )
    val missingConstructors =
      retrieveDatatypes( problem, matchedType.name )
        .constructors
        .filter {
          constructor => !coveredConstructors.contains( constructor.name )
        }
    val defaultExpr = cases.filter {
      case TipSmtCase( TipSmtDefault, _ ) => true
      case _                              => false
    }.head.expr
    val generatedCases = missingConstructors map {
      generateCase( _, visibleVariables, defaultExpr )
    }
    val oldCases = tipSmtMatch.cases filter { _.pattern != TipSmtDefault }

    TipSmtMatch( tipSmtMatch.expr, oldCases ++ generatedCases )
  }

  /**
   * Generates the case statement for the given constructor.
   *
   * @param tipSmtConstructor The constructor for which the case statement is
   *                          to be generated.
   * @param visibleVariables The variables visible to the generated case
   *                         statement.
   * @param defaultExpression The expression to be used by the case statement.
   * @return A case-statement for the given constructor and the given
   *         expression.
   */
  private def generateCase(
    tipSmtConstructor: TipSmtConstructor,
    visibleVariables:  Seq[String],
    defaultExpression: TipSmtExpression ): TipSmtCase = {
    val nameGenerator = new NameGenerator( visibleVariables )
    TipSmtCase(
      TipSmtConstructorPattern(
        TipSmtIdentifier( tipSmtConstructor.name ),
        tipSmtConstructor.fields.map {
          _ => TipSmtIdentifier( nameGenerator.fresh( "x" ) )
        } ),
      defaultExpression )
  }

  /**
   * Retrieves the names of the constructors covered by the given case
   * statements.
   *
   * @param cases The case statements whose covered constructors are to be
   *              computed.
   * @return The names of the covered constructors.
   */
  private def coveredConstrs(
    cases: Seq[TipSmtCase] ): Seq[String] = {
    cases map { _.pattern } filter {
      case TipSmtDefault => false
      case TipSmtConstructorPattern( constructor, _ ) =>
        problem.symbolTable.get.contains( constructor.name )
    } map {
      case TipSmtConstructorPattern( constructor, _ ) =>
        constructor.name
      case _ => throw new IllegalStateException()
    }
  }
}

