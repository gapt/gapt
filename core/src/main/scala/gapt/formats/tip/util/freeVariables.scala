package gapt.formats.tip.util

import gapt.formats.tip.parser.TipSmtAnd
import gapt.formats.tip.parser.TipSmtCase
import gapt.formats.tip.parser.TipSmtConstructorPattern
import gapt.formats.tip.parser.TipSmtEq
import gapt.formats.tip.parser.TipSmtExists
import gapt.formats.tip.parser.TipSmtExpression
import gapt.formats.tip.parser.TipSmtFalse
import gapt.formats.tip.parser.TipSmtForall
import gapt.formats.tip.parser.TipSmtFun
import gapt.formats.tip.parser.TipSmtIdentifier
import gapt.formats.tip.parser.TipSmtImp
import gapt.formats.tip.parser.TipSmtIte
import gapt.formats.tip.parser.TipSmtMatch
import gapt.formats.tip.parser.TipSmtNot
import gapt.formats.tip.parser.TipSmtOr
import gapt.formats.tip.parser.TipSmtProblem
import gapt.formats.tip.parser.TipSmtTrue

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