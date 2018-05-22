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
import gapt.formats.tip.parser.TipSmtVariableDecl
import gapt.utils.NameGenerator

/**
 * This class implements substitution for TIP problems.
 *
 * @param problem The problem in which substitutions are to be carried out.
 */
class TipSubstitute( val problem: TipSmtProblem ) {

  /**
   * Renames the variables introduced by a case-statement away from
   * blacklisted names.
   *
   * @param tipSmtCase The case-statement in which variables are to be renamed.
   * @param blacklist The blacklisted names.
   * @return An equivalent case-statement whose bound variables do not intersect
   *         the blacklist.
   */
  def awayFrom(
    tipSmtCase: TipSmtCase,
    blacklist:  Seq[String] ): TipSmtCase = {
    val TipSmtConstructorPattern( constructor, fields ) = tipSmtCase.pattern
    val oldNames = fields.map { _.name }
    val nameGenerator = new NameGenerator(
      constructor.name +: ( oldNames ++ blacklist ) )
    val newNames =
      oldNames map { oldName =>
        if ( blacklist.contains( oldName ) ) {
          nameGenerator.fresh( oldName )
        } else {
          oldName
        }
      }
    caseChangeVariableNames( tipSmtCase, oldNames, newNames )
  }

  /**
   * Substitutes a name by a given expression.
   *
   * @param expr The expression in which the substitution is to be carried out.
   * @param oldName The name that is to be substituted for replacement
   * @param replacement The expression that is to be inserted at free
   *                    occurrences of oldName.
   * @return An expression that is equivalent to expr[oldName/replacement].
   */
  def apply(
    expr:        TipSmtExpression,
    oldName:     String,
    replacement: TipSmtExpression ): TipSmtExpression = {
    expr match {
      case expr @ TipSmtAnd( _ ) =>
        TipSmtAnd( expr.exprs map { apply( _, oldName, replacement ) } )

      case expr @ TipSmtOr( _ ) =>
        TipSmtOr( expr.exprs map { apply( _, oldName, replacement ) } )

      case expr @ TipSmtImp( _ ) =>
        TipSmtImp( expr.exprs map { apply( _, oldName, replacement ) } )

      case expr @ TipSmtEq( _ ) =>
        TipSmtEq( expr.exprs map { apply( _, oldName, replacement ) } )

      case expr @ TipSmtForall( _, _ ) =>
        substituteQuantifiedExpression(
          oldName, replacement, expr.variables, expr.formula, TipSmtForall )

      case expr @ TipSmtExists( _, _ ) =>
        substituteQuantifiedExpression(
          oldName, replacement, expr.variables, expr.formula, TipSmtExists )

      case expr @ TipSmtIte( _, _, _ ) =>
        substitute( oldName, replacement, expr )

      case expr @ TipSmtMatch( _, _ ) =>
        substitute( oldName, replacement, expr )

      case TipSmtFun( funName, arguments ) =>
        TipSmtFun(
          funName, arguments map { apply( _, oldName, replacement ) } )

      case expr @ TipSmtNot( _ ) =>
        TipSmtNot( apply( expr.expr, oldName, replacement ) )

      case identifier @ TipSmtIdentifier( name ) =>
        if ( name == oldName )
          replacement
        else
          identifier

      case TipSmtTrue =>
        TipSmtTrue

      case TipSmtFalse =>
        TipSmtFalse
    }
  }

  /**
   * Substitutes a name by a given expression.
   *
   * @param expr The expression in which the substitution is to be carried out.
   * @param oldName The name that is to be substituted for replacement
   * @param replacement The expression that is to be inserted at free
   *                    occurrences of oldName.
   * @return An expression that is equivalent to expr[oldName/replacement].
   */
  private def substitute(
    oldName:     String,
    replacement: TipSmtExpression,
    expr:        TipSmtMatch ): TipSmtExpression =
    TipSmtMatch(
      apply( expr.expr, oldName, replacement ),
      expr.cases map { substCase( _, oldName, replacement ) } )

  /**
   * Substitutes a name by a given expression.
   *
   * @param expr The expression in which the substitution is to be carried out.
   * @param oldName The name that is to be substituted for replacement
   * @param replacement The expression that is to be inserted at free
   *                    occurrences of oldName.
   * @return An expression that is equivalent to expr[oldName/replacement].
   */
  private def substitute(
    oldName:     String,
    replacement: TipSmtExpression,
    expr:        TipSmtIte ): TipSmtExpression =
    TipSmtIte(
      apply( expr.cond, oldName, replacement ),
      apply( expr.the, oldName, replacement ),
      apply( expr.els, oldName, replacement ) )

  /**
   * Abstracts the constructors TipSmtForall and TipSmtExists.
   */
  type QuantifiedExpressionConstructor = //
  ( Seq[TipSmtVariableDecl], TipSmtExpression ) => TipSmtExpression

  /**
   * Substitutes a name for an expression in a quantified expression.
   *
   * @param oldName The name to be replaced by replacement.
   * @param replacement The expression to be inserted at free occurrences of
   *                    oldName.
   * @param variables The variables bound by the quantifier.
   * @param formula The expression over which the quantifier ranges.
   * @param quantifier The quantifier's constructor.
   * @return An expression equivalent to Q(X)(E)[y/R], where Q is the
   *         quantifier, X are the bound variables, E is the expression over
   *         which the quantifier ranges, y the variable to be substituted by
   *         the expression R.
   */
  private def substituteQuantifiedExpression(
    oldName:     String,
    replacement: TipSmtExpression,
    variables:   Seq[TipSmtVariableDecl],
    formula:     TipSmtExpression,
    quantifier:  QuantifiedExpressionConstructor ): TipSmtExpression = {
    val quantifiedVariables = variables.map { _.name }
    if ( quantifiedVariables.contains( oldName ) ) {
      quantifier( variables, formula )
    } else if ( quantifiedVariables
      .toSet
      .intersect( freeVariables( problem, replacement ) )
      .nonEmpty ) {
      val nameGenerator =
        new NameGenerator(
          freeVariables( problem, formula ) ++
            Seq( oldName ) ++
            freeVariables( problem, replacement ) )

      val newQuantifiedVariables = variables.map { v =>
        if ( freeVariables( problem, replacement ).contains( v.name ) )
          TipSmtVariableDecl( nameGenerator.fresh( v.name ), v.typ )
        else
          v
      }

      val newFormula =
        quantifiedVariables
          .zip( newQuantifiedVariables.map { _.name } )
          .foldRight( formula ) {
            case ( ( oldName, newName ), formula ) =>
              apply( formula, oldName, TipSmtIdentifier( newName ) )
          }

      val newExpression = TipSmtExists(
        newQuantifiedVariables,
        newFormula )

      apply( newExpression, oldName, replacement )
    } else {
      TipSmtExists(
        variables, apply( formula, oldName, replacement ) )
    }
  }

  /**
   * Substitutes a name by a given expression.
   *
   * @param cas The expression in which the substitution is to be carried out.
   * @param oldName The name that is to be substituted for replacement
   * @param replacement The expression that is to be inserted at free
   *                    occurrences of oldName.
   * @return An expression that is equivalent to expr[oldName/replacement].
   */
  private def substCase(
    cas:         TipSmtCase,
    oldName:     String,
    replacement: TipSmtExpression ): TipSmtCase = {
    val TipSmtConstructorPattern( constructor, identifiers ) = cas.pattern
    val boundNames = identifiers.map { _.name }
    if ( boundNames.contains( oldName ) ) {
      cas
    } else if ( boundNames
      .toSet
      .intersect( freeVariables( problem, replacement ) )
      .nonEmpty ) {
      val nameGenerator =
        new NameGenerator(
          freeVariables( problem, cas.expr ) ++
            Seq( oldName ) ++
            freeVariables( problem, replacement ) )
      val newBoundNames = boundNames map { boundName =>
        if ( freeVariables( problem, replacement ).contains( boundName ) ) {
          nameGenerator.fresh( boundName )
        } else {
          boundName
        }
      }
      substCase(
        caseChangeVariableNames( cas, boundNames, newBoundNames ),
        oldName,
        replacement )
    } else {
      TipSmtCase( cas.pattern, apply( cas.expr, oldName, replacement ) )
    }
  }

  /**
   * Renames the fields in a case-statement.
   *
   * @param tipSmtCase The case-statement in which the fields are to be renamed.
   * @param oldNames The names of the fields in the given case-statement.
   * @param newBoundNames The new names for the fields.
   * @return An equivalent case-statement whose fields have been renamed to
   *         the new names. This function assumes that only fields that are
   *         variables receive new names.
   */
  private def caseChangeVariableNames(
    tipSmtCase:    TipSmtCase,
    oldNames:      Seq[String],
    newBoundNames: Seq[String] ): TipSmtCase = {
    val TipSmtConstructorPattern( constructor, fields ) = tipSmtCase.pattern
    val newPattern = TipSmtConstructorPattern(
      constructor,
      newBoundNames.map { TipSmtIdentifier } )
    val newExpression = oldNames.zip( newBoundNames )
      .foldRight( tipSmtCase.expr )( {
        case ( ( oldName, newName ), cas ) =>
          apply( cas, oldName, TipSmtIdentifier( newName ) )
      } )
    TipSmtCase( newPattern, newExpression )
  }
}