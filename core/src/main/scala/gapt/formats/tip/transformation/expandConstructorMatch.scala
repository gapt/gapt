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
  def transform( problem: TipSmtProblem ): TipSmtProblem =
    new ExpandConstructorMatch( problem )()
}

class ExpandConstructorMatch( val problem: TipSmtProblem ) {

  problem.symbolTable = Some( SymbolTable( problem ) )

  private val constructorSymbols: Set[String] =
    problem.symbolTable.get.constructors

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
        retrieveCase( matchExpression, id ).expr
    }

  private def expandConstructorMatch(
    expr: TipSmtAnd ): TipSmtExpression =
    expr.copy( exprs = expr.exprs map { expandConstructorMatch } )

  private def expandConstructorMatch(
    expr: TipSmtOr ): TipSmtExpression =
    expr.copy( exprs = expr.exprs map { expandConstructorMatch } )

  private def expandConstructorMatch(
    expr: TipSmtEq ): TipSmtExpression =
    expr.copy( exprs = expr.exprs map { expandConstructorMatch } )

  private def expandConstructorMatch(
    expr: TipSmtImp ): TipSmtExpression =
    expr.copy( exprs = expr.exprs map { expandConstructorMatch } )

  private def expandConstructorMatch(
    expr: TipSmtIte ): TipSmtExpression =
    TipSmtIte(
      expandConstructorMatch( expr.cond ),
      expandConstructorMatch( expr.ifTrue ),
      expandConstructorMatch( expr.ifFalse ) )

  private def expandConstructorMatch(
    expr: TipSmtExists ): TipSmtExpression =
    expr.copy( formula = expandConstructorMatch( expr.formula ) )

  private def expandConstructorMatch(
    expr: TipSmtForall ): TipSmtExpression =
    expr.copy( formula = expandConstructorMatch( expr.formula ) )

  private def expandConstructorMatch(
    expr: TipSmtFun ): TipSmtExpression =
    expr.copy( arguments = expr.arguments map { expandConstructorMatch } )

  private def retrieveCase(
    matchExpression: TipSmtMatch, constructor: TipSmtIdentifier ): TipSmtCase =
    retrieveCase( matchExpression, constructor.name )

  private def retrieveCase(
    matchExpression: TipSmtMatch, constructor: String ): TipSmtCase =
    matchExpression.cases.filter {
      case TipSmtCase( TipSmtConstructorPattern( TipSmtIdentifier( symbol ), _ ), _ ) if constructor == symbol => true
      case _ => false
    } head

  private def isConstructor( symbol: TipSmtIdentifier ): Boolean =
    isConstructor( symbol.name )

  private def isConstructor( symbol: String ): Boolean =
    constructorSymbols.contains( symbol )
}
