package gapt.formats.tip.util

import gapt.formats.tip.parser._

object freeVariables {
  def apply(
    problem:    TipSmtProblem,
    expression: TipSmtExpression ): Set[String] = {
    ( new FreeVariables( problem ) ).freeVariables( expression )
  }
}

class FreeVariables( problem: TipSmtProblem ) {
  def freeVariables(
    expression: TipSmtExpression ): Set[String] = {
    expression match {
      case expr @ TipSmtAnd( _ ) =>
        expr.exprs.flatMap( freeVariables ).toSet

      case expr @ TipSmtOr( _ ) =>
        expr.exprs.flatMap( freeVariables ).toSet

      case expr @ TipSmtImp( _ ) =>
        expr.exprs.flatMap( freeVariables ).toSet

      case expr @ TipSmtEq( _ ) =>
        expr.exprs.flatMap( freeVariables ).toSet

      case TipSmtForall( boundVariables, formula ) =>
        freeVariables( formula ).diff( boundVariables.map {
          _.name
        } toSet )

      case TipSmtExists( boundVariables, formula ) =>
        freeVariables( formula ).diff( boundVariables.map {
          _.name
        } toSet )

      case expr @ TipSmtIte( _, _, _ ) =>
        freeVariables( expr.cond ) ++
          freeVariables( expr.the ) ++
          freeVariables( expr.els )

      case TipSmtMatch( matchedExpression, cases ) =>
        freeVariables( matchedExpression ) ++
          cases.flatMap( freeVariablesCase )

      case expr @ TipSmtFun( _, _ ) =>
        expr.arguments.flatMap( freeVariables ).toSet

      case expr @ TipSmtNot( _ ) =>
        freeVariables( expr.expr )

      case expr @ TipSmtIdentifier( _ ) =>
        if ( problem.symbolTable.get.contains( expr.name ) )
          Set()
        else
          Set( expr.name )

      case TipSmtTrue  => Set()
      case TipSmtFalse => Set()
    }
  }

  def freeVariablesCase(
    tipSmtCase: TipSmtCase ): Set[String] = {
    val TipSmtConstructorPattern( constructor, fields ) = tipSmtCase.pattern
    val boundVariables =
      ( constructor.name +: fields.map( _.name ) )
        .filter( isVariable )
        .toSet
    freeVariables( tipSmtCase.expr ).diff( boundVariables )
  }

  def isVariable( name: String ): Boolean =
    !problem.symbolTable.get.contains( name )
}