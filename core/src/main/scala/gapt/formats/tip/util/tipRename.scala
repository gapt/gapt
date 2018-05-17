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
import gapt.formats.tip.parser.TipSmtTrue
import gapt.formats.tip.parser.TipSmtVariableDecl
import gapt.utils.NameGenerator

object tipRename {

  def awayFrom(
    tipSmtCase: TipSmtCase,
    blacklist:  Seq[String] ): TipSmtCase = {
    val TipSmtConstructorPattern( constructor, fields ) = tipSmtCase.pattern
    val conflictVariables =
      ( constructor +: fields )
        .map { _.name }
        .toSet
        .intersect( blacklist.toSet )
    awayFrom( tipSmtCase, conflictVariables.toSeq, blacklist )
  }

  def awayFrom(
    tipSmtCase: TipSmtCase,
    variables:  Seq[String],
    blacklist:  Seq[String] ): TipSmtCase = {
    val TipSmtConstructorPattern( constructor, identifiers ) =
      tipSmtCase.pattern
    val nameGenerator = new NameGenerator(
      constructor.name +: ( identifiers.map { _.name } ++ blacklist ) )
    val renaming = variables map { v => ( v, nameGenerator.fresh( v ) ) }
    renaming.foldRight( tipSmtCase )( {
      case ( ( oldName, newName ), cas ) =>
        tipRename.caseChangeVariableName( cas, oldName, newName )
    } )
  }

  def apply(
    expr:    TipSmtExpression,
    oldName: String,
    newName: String ): TipSmtExpression = {
    expr match {
      case expr @ TipSmtAnd( _ ) =>
        TipSmtAnd( expr.exprs map { tipRename( _, oldName, newName ) } )

      case expr @ TipSmtOr( _ ) =>
        TipSmtOr( expr.exprs map { tipRename( _, oldName, newName ) } )

      case expr @ TipSmtImp( _ ) =>
        TipSmtImp( expr.exprs map { tipRename( _, oldName, newName ) } )

      case expr @ TipSmtEq( _ ) =>
        TipSmtEq( expr.exprs map { tipRename( _, oldName, newName ) } )

      case expr @ TipSmtForall( _, _ ) =>
        renameQuantifiedExpression(
          oldName, newName, expr.variables, expr.formula, TipSmtExists )

      case expr @ TipSmtExists( _, _ ) =>
        renameQuantifiedExpression(
          oldName, newName, expr.variables, expr.formula, TipSmtExists )

      case expr @ TipSmtIte( _, _, _ ) =>
        renameIteExpression(oldName, newName, expr)

      case expr @ TipSmtMatch( _, _ ) =>
        renameMatchExpression(oldName, newName, expr)

      case TipSmtFun( funName, arguments ) =>
        TipSmtFun( funName, arguments map { tipRename( _, oldName, newName ) } )

      case expr @ TipSmtNot( _ ) =>
        TipSmtNot( tipRename( expr.expr, oldName, newName ) )

      case identifier @ TipSmtIdentifier( name ) =>
        if ( name == oldName )
          TipSmtIdentifier( newName )
        else
          identifier

      case TipSmtTrue =>
        TipSmtTrue

      case TipSmtFalse =>
        TipSmtFalse
    }
  }

  private def renameMatchExpression(
    oldName: String, newName: String, expr: TipSmtMatch): TipSmtExpression =
    TipSmtMatch(
      tipRename( expr.expr, oldName, newName ),
      expr.cases map { renameCase( _, oldName, newName ) } )

  private def renameIteExpression(
    oldName: String, newName: String, expr: TipSmtIte): TipSmtExpression =
    TipSmtIte(
      tipRename( expr.cond, oldName, newName ),
      tipRename( expr.the, oldName, newName ),
      tipRename( expr.els, oldName, newName ) )

  type QuantifiedExpressionConstructor = //
  ( Seq[TipSmtVariableDecl], TipSmtExpression ) => TipSmtExpression

  private def renameQuantifiedExpression(
    oldName:    String,
    newName:    String,
    variables:  Seq[TipSmtVariableDecl],
    formula:    TipSmtExpression,
    quantifier: QuantifiedExpressionConstructor ): TipSmtExpression = {
    val quantifiedVariables = variables.map { _.name }
    if ( quantifiedVariables.contains( oldName ) ) {
      quantifier( variables, formula )
    } else if ( quantifiedVariables.contains( newName ) ) {
      val nameGenerator =
        new NameGenerator( quantifiedVariables ++ Seq( oldName, newName ) )
      val newQuantifiedName = nameGenerator.fresh( newName )
      val newQuantifiedVariables = variables.map { v =>
        if ( v.name == newName )
          TipSmtVariableDecl( newQuantifiedName, v.typ )
        else
          v
      }
      val newExpression =
        TipSmtExists(
          newQuantifiedVariables,
          tipRename( formula, newName, newQuantifiedName ) )
      tipRename( newExpression, oldName, newName )
    } else {
      TipSmtExists(
        variables, tipRename( formula, oldName, newName ) )
    }
  }

  private def renameCase(
    cas: TipSmtCase, oldName: String, newName: String ): TipSmtCase = {
    val TipSmtConstructorPattern( constructor, identifiers ) = cas.pattern
    val boundNames = constructor.name +: identifiers.map { _.name }
    if ( boundNames.contains( oldName ) ) {
      cas
    } else if ( boundNames.contains( newName ) ) {
      val nameGenerator =
        new NameGenerator( boundNames ++ Seq( oldName, newName ) )
      val newBoundName = nameGenerator.fresh( newName )
      caseChangeVariableName( cas, newName, newBoundName )
    } else {
      TipSmtCase( cas.pattern, tipRename( cas.expr, oldName, newName ) )
    }
  }

  private def caseChangeVariableName(
    tipSmtCase: TipSmtCase, oldName: String, newName: String ): TipSmtCase = {
    val TipSmtConstructorPattern( constructor, fields ) = tipSmtCase.pattern
    val newPattern = TipSmtConstructorPattern(
      if ( constructor.name == oldName )
        TipSmtIdentifier( newName )
      else
        constructor,
      fields map { id =>
        if ( id.name == oldName )
          TipSmtIdentifier( newName )
        else
          id
      } )
    val newExpression = tipRename( tipSmtCase.expr, oldName, newName )
    TipSmtCase( newPattern, newExpression )
  }
}