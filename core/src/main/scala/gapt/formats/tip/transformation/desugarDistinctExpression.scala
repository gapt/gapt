package gapt.formats.tip.transformation

import gapt.formats.tip.parser.TipSmtAnd
import gapt.formats.tip.parser.TipSmtAssertion
import gapt.formats.tip.parser.TipSmtCase
import gapt.formats.tip.parser.TipSmtDistinct
import gapt.formats.tip.parser.TipSmtEq
import gapt.formats.tip.parser.TipSmtExists
import gapt.formats.tip.parser.TipSmtExpression
import gapt.formats.tip.parser.TipSmtForall
import gapt.formats.tip.parser.TipSmtFun
import gapt.formats.tip.parser.TipSmtFunctionDefinition
import gapt.formats.tip.parser.TipSmtGoal
import gapt.formats.tip.parser.TipSmtImp
import gapt.formats.tip.parser.TipSmtIte
import gapt.formats.tip.parser.TipSmtMatch
import gapt.formats.tip.parser.TipSmtMutualRecursiveFunctionDefinition
import gapt.formats.tip.parser.TipSmtNot
import gapt.formats.tip.parser.TipSmtOr
import gapt.formats.tip.parser.TipSmtProblem

object desugarDistinctExpressions extends TipSmtProblemTransformation {
  override def transform( problem: TipSmtProblem ): TipSmtProblem =
    new DesugarDistinctExpression( problem )()
}

class DesugarDistinctExpression( problem: TipSmtProblem ) {

  def apply(): TipSmtProblem = {
    problem.copy( definitions = problem.definitions map {
      case d @ TipSmtFunctionDefinition( _, _, _, _, _ ) =>
        apply( d )
      case d @ TipSmtMutualRecursiveFunctionDefinition( _ ) =>
        d.copy( functions = d.functions.map { apply } )
      case d @ TipSmtGoal( _, _ ) =>
        d.copy( expr = desugarDistinctConstruct( d.expr ) )
      case d @ TipSmtAssertion( _, _ ) =>
        d.copy( expr = desugarDistinctConstruct( d.expr ) )
      case d => d
    } )
  }

  def apply( function: TipSmtFunctionDefinition ): TipSmtFunctionDefinition =
    function.copy( body = desugarDistinctConstruct( function.body ) )

  def desugarDistinctConstruct(
    expression: TipSmtExpression ): TipSmtExpression = {
    expression match {
      case e @ TipSmtAnd( _ ) =>
        e.copy( exprs = e.exprs map { desugarDistinctConstruct } )
      case e @ TipSmtOr( _ ) =>
        e.copy( exprs = e.exprs map { desugarDistinctConstruct } )
      case e @ TipSmtImp( _ ) =>
        e.copy( exprs = e.exprs map { desugarDistinctConstruct } )
      case e @ TipSmtEq( _ ) =>
        e.copy( exprs = e.exprs map { desugarDistinctConstruct } )
      case e @ TipSmtForall( _, _ ) =>
        e.copy( formula = desugarDistinctConstruct( e.formula ) )
      case e @ TipSmtExists( _, _ ) =>
        e.copy( formula = desugarDistinctConstruct( e.formula ) )
      case e @ TipSmtDistinct( _ ) =>
        desugarDistinctConstruct( e )
      case e @ TipSmtFun( _, _ ) =>
        e.copy( arguments = e.arguments.map { desugarDistinctConstruct } )
      case e @ TipSmtNot( _ ) =>
        e.copy( expr = desugarDistinctConstruct( e.expr ) )
      case e @ TipSmtIte( _, _, _ ) =>
        TipSmtIte(
          desugarDistinctConstruct( e.cond ),
          desugarDistinctConstruct( e.ifTrue ),
          desugarDistinctConstruct( e.ifFalse ) )
      case e @ TipSmtMatch( _, _ ) =>
        e.copy(
          expr = desugarDistinctConstruct( e.expr ),
          cases = e.cases map { desugarDistinctConstruct } )
      case e => e
    }
  }

  private def desugarDistinctConstruct(
    expression: TipSmtDistinct ): TipSmtExpression = {
    val newExpressions = expression.expressions.map { desugarDistinctConstruct }
    TipSmtAnd( pairAll( newExpressions ) map {
      case ( l, r ) => TipSmtNot( TipSmtEq( Seq( l, r ) ) )
    } )
  }

  private def desugarDistinctConstruct(
    tipSmtCase: TipSmtCase ): TipSmtCase = {
    tipSmtCase.copy( expr = desugarDistinctConstruct( tipSmtCase.expr ) )
  }

  private def pairAll[T]( elements: Seq[T] ): Seq[( T, T )] =
    elements
      .tails
      .toList
      .init
      .flatMap { es => es.tail.map { ( es.head, _ ) } }
}
