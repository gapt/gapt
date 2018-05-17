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
import gapt.formats.tip.parser.TipSmtOr
import gapt.formats.tip.parser.TipSmtProblem
import gapt.utils.NameGenerator

class TipSmtDefaultPatternExpansion( problem: TipSmtProblem ) {

  def apply(): Unit = {
    problem.definitions foreach {
      case TipSmtFunctionDefinition( _, _, parameters, _, body ) =>
        val context = parameters map {
          _.name
        }
        exandDefaultPatterns( body, context )
      case TipSmtGoal( _, expression ) =>
        exandDefaultPatterns( expression, Seq() )
      case TipSmtAssertion( _, expression ) =>
        exandDefaultPatterns( expression, Seq() )
      case _ =>
    }
  }

  private def exandDefaultPatterns(
    expr:             TipSmtExpression,
    visibleVariables: Seq[String] ): Unit = expr match {
    case TipSmtAnd( subexpressions ) =>
      subexpressions foreach {
        exandDefaultPatterns( _, visibleVariables )
      }
    case TipSmtOr( subexpressions ) =>
      subexpressions foreach {
        exandDefaultPatterns( _, visibleVariables )
      }
    case TipSmtImp( subexpressions ) =>
      subexpressions foreach {
        exandDefaultPatterns( _, visibleVariables )
      }
    case TipSmtFun( _, arguments ) =>
      arguments foreach {
        exandDefaultPatterns( _, visibleVariables )
      }
    case TipSmtForall( vars, subexpression ) =>
      exandDefaultPatterns(
        subexpression,
        visibleVariables ++ vars.map( _.name ) )
    case TipSmtExists( vars, subexpression ) =>
      exandDefaultPatterns(
        subexpression,
        visibleVariables ++ vars.map( _.name ) )
    case matchExpr @ TipSmtMatch( _, _ ) =>
      if ( containsDefaultPattern( matchExpr ) ) {
        expandDefaultPattern( matchExpr, visibleVariables )
      }
      matchExpr.cases foreach {
        expandDefaultPatternCaseStatement( _, visibleVariables )
      }
    case TipSmtIte( expr1, expr2, expr3 ) =>
      exandDefaultPatterns( expr1, visibleVariables )
      exandDefaultPatterns( expr2, visibleVariables )
      exandDefaultPatterns( expr3, visibleVariables )
    case _ =>
  }

  private def expandDefaultPatternCaseStatement(
    cas:              TipSmtCase,
    visibleVariables: Seq[String] ): Unit = {
    cas.pattern match {
      case TipSmtConstructorPattern( _, fields ) =>
        val variableFields = fields
          .map { _.name }
          .filter { !problem.symbolTable.get.contains( _ ) }
        exandDefaultPatterns(
          cas.expr, visibleVariables ++ variableFields )
      case _ => throw new IllegalStateException()
    }
  }

  private def containsDefaultPattern( tipSmtMatch: TipSmtMatch ): Boolean = {
    tipSmtMatch.cases.exists { _.pattern == TipSmtDefault }
  }

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

