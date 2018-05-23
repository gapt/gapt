package gapt.formats.tip.transformation

import gapt.formats.tip.analysis.retrieveDatatypes
import gapt.formats.tip.parser.TipSmtAnd
import gapt.formats.tip.parser.TipSmtAssertion
import gapt.formats.tip.parser.TipSmtCase
import gapt.formats.tip.parser.TipSmtConstructor
import gapt.formats.tip.parser.TipSmtConstructorPattern
import gapt.formats.tip.parser.TipSmtDefault
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
import gapt.utils.NameGenerator

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

  /**
   * Expands all default patterns in the given problem. The expansion takes
   * place in the input problem.
   */
  def apply(): Unit = {
    problem.definitions foreach {
      case fun @ TipSmtFunctionDefinition( _, _, _, _, _ ) =>
        apply( fun )
      case TipSmtGoal( _, expression ) =>
        expandDefaultPatterns( expression, Seq() )
      case funDefs @ TipSmtMutualRecursiveFunctionDefinition( _ ) =>
        funDefs.functions.foreach { apply }
      case TipSmtAssertion( _, expression ) =>
        expandDefaultPatterns( expression, Seq() )
      case _ =>
    }
  }

  private def apply(
    fun: TipSmtFunctionDefinition ): Unit = {
    val context = fun.parameters map {
      _.name
    }
    expandDefaultPatterns( fun.body, context )
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
    visibleVariables: Seq[String] ): Unit = expr match {
    case TipSmtAnd( subexpressions ) =>
      subexpressions foreach {
        expandDefaultPatterns( _, visibleVariables )
      }
    case TipSmtOr( subexpressions ) =>
      subexpressions foreach {
        expandDefaultPatterns( _, visibleVariables )
      }
    case TipSmtImp( subexpressions ) =>
      subexpressions foreach {
        expandDefaultPatterns( _, visibleVariables )
      }
    case TipSmtFun( _, arguments ) =>
      arguments foreach {
        expandDefaultPatterns( _, visibleVariables )
      }
    case TipSmtForall( vars, subexpression ) =>
      expandDefaultPatterns(
        subexpression,
        visibleVariables ++ vars.map( _.name ) )
    case TipSmtExists( vars, subexpression ) =>
      expandDefaultPatterns(
        subexpression,
        visibleVariables ++ vars.map( _.name ) )
    case matchExpr @ TipSmtMatch( _, _ ) =>
      if ( containsDefaultPattern( matchExpr ) ) {
        expandDefaultPattern( matchExpr, visibleVariables )
      }
      matchExpr.cases foreach {
        expandDefaultPatterns( _, visibleVariables )
      }
    case TipSmtIte( expr1, expr2, expr3 ) =>
      expandDefaultPatterns( expr1, visibleVariables )
      expandDefaultPatterns( expr2, visibleVariables )
      expandDefaultPatterns( expr3, visibleVariables )
    case _ =>
  }

  /**
   * Expands default patterns in the given case statement.
   *
   * @param cas The case statement whose default patterns are expanded.
   * @param visibleVariables The variables visible to this case statement.
   */
  private def expandDefaultPatterns(
    cas:              TipSmtCase,
    visibleVariables: Seq[String] ): Unit = {
    cas.pattern match {
      case TipSmtConstructorPattern( _, fields ) =>
        val variableFields = fields
          .map { _.name }
          .filter { !problem.symbolTable.get.contains( _ ) }
        expandDefaultPatterns(
          cas.expr, visibleVariables ++ variableFields )
      case _ => throw new IllegalStateException()
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
    visibleVariables: Seq[String] ): Unit = {
    val TipSmtMatch( matchedExpression, cases ) = tipSmtMatch
    val Some( matchedType ) = tipSmtMatch.expr.datatype
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
    tipSmtMatch.cases = tipSmtMatch.cases filter { _.pattern != TipSmtDefault }
    tipSmtMatch.cases ++= generatedCases
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

