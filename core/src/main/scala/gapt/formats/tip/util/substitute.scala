package gapt.formats.tip.util

import gapt.formats.tip.parser.TipSmtAnd
import gapt.formats.tip.parser.TipSmtCase
import gapt.formats.tip.parser.TipSmtConstructorPattern
import gapt.formats.tip.parser.TipSmtDistinct
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

  type Substitution = Map[TipSmtIdentifier, TipSmtExpression]

  def apply(
    expr:     TipSmtExpression,
    variable: String,
    term:     TipSmtExpression ): TipSmtExpression =
    apply( expr, Map( TipSmtIdentifier( variable ) -> term ) )

  /**
   * Substitutes a name by a given expression.
   *
   * @param expr The expression in which the substitution is to be carried out.
   * @param substitution The substitution that is to be applied to the
   * expression
   * @return An expression that is equivalent to expr[oldName/replacement].
   */
  def apply(
    expr:         TipSmtExpression,
    substitution: Substitution ): TipSmtExpression = {
    expr match {
      case expr @ TipSmtAnd( _ ) =>
        TipSmtAnd( expr.exprs map { apply( _, substitution ) } )

      case expr @ TipSmtOr( _ ) =>
        TipSmtOr( expr.exprs map { apply( _, substitution ) } )

      case expr @ TipSmtImp( _ ) =>
        TipSmtImp( expr.exprs map { apply( _, substitution ) } )

      case expr @ TipSmtEq( _ ) =>
        TipSmtEq( expr.exprs map { apply( _, substitution ) } )

      case expr @ TipSmtDistinct( _ ) =>
        TipSmtDistinct(
          expr.expressions map { apply( _, substitution ) } )

      case expr @ TipSmtForall( _, _ ) =>
        substituteQuantifiedExpression(
          substitution, expr.variables, expr.formula, TipSmtForall )

      case expr @ TipSmtExists( _, _ ) =>
        substituteQuantifiedExpression(
          substitution, expr.variables, expr.formula, TipSmtExists )

      case expr @ TipSmtIte( _, _, _ ) =>
        substitute( substitution, expr )

      case expr @ TipSmtMatch( _, _ ) =>
        substitute( substitution, expr )

      case TipSmtFun( funName, arguments ) =>
        TipSmtFun(
          funName, arguments map { apply( _, substitution ) } )

      case expr @ TipSmtNot( _ ) =>
        TipSmtNot( apply( expr.expr, substitution ) )

      case identifier @ TipSmtIdentifier( _ ) =>
        substitution.get( identifier ) match {
          case Some( replacement ) => replacement
          case _                   => identifier
        }

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
   * @param substitution The substitution that is to be applied to the
   * expression
   * @return An expression that is equivalent to expr[oldName/replacement].
   */
  private def substitute(
    substitution: Substitution,
    expr:         TipSmtMatch ): TipSmtExpression =
    TipSmtMatch(
      apply( expr.expr, substitution ),
      expr.cases map { substCase( _, substitution ) } )

  /**
   * Substitutes a name by a given expression.
   *
   * @param expr The expression in which the substitution is to be carried out.
   * @param substitution The substitution that is to be applied to the
   * expression
   * @return An expression that is equivalent to expr[oldName/replacement].
   */
  private def substitute(
    substitution: Substitution,
    expr:         TipSmtIte ): TipSmtExpression =
    TipSmtIte(
      apply( expr.cond, substitution ),
      apply( expr.ifTrue, substitution ),
      apply( expr.ifFalse, substitution ) )

  /**
   * Abstracts the constructors TipSmtForall and TipSmtExists.
   */
  type QuantifiedExpressionConstructor = //
  ( Seq[TipSmtVariableDecl], TipSmtExpression ) => TipSmtExpression

  /**
   * Substitutes a name for an expression in a quantified expression.
   *
   * @param substitution The substitution that is to be applied to the
   * expression
   * @param variables The variables bound by the quantifier.
   * @param formula The expression over which the quantifier ranges.
   * @param quantifier The quantifier's constructor.
   * @return An expression equivalent to Q(X)(E)[y/R], where Q is the
   *         quantifier, X are the bound variables, E is the expression over
   *         which the quantifier ranges, y the variable to be substituted by
   *         the expression R.
   */
  private def substituteQuantifiedExpression(
    substitution: Substitution,
    variables:    Seq[TipSmtVariableDecl],
    formula:      TipSmtExpression,
    quantifier:   QuantifiedExpressionConstructor ): TipSmtExpression = {

    val newSubstitution: Substitution = substitution.filter {
      case ( identifier, _ ) =>
        !variables.map { _.name }.contains( identifier.name )
    }

    val substFreeVars: Set[String] =
      newSubstitution.values.flatMap { freeVariables( problem, _ ) } toSet

    val nameGenerator =
      new NameGenerator(
        substFreeVars ++
          newSubstitution.keys.map { _.name } ++
          freeVariables( problem, formula ) )

    val newQuantifiedVariables = variables.map {
      v =>
        if ( substFreeVars.contains( v.name ) )
          TipSmtVariableDecl( nameGenerator.fresh( v.name ), v.typ )
        else
          v
    }

    val variableSubstitution: Substitution =
      Map[TipSmtIdentifier, TipSmtExpression](
        variables
          .map { v => TipSmtIdentifier( v.name ) }
          .zip(
            newQuantifiedVariables
              .map { v => TipSmtIdentifier( v.name ) } ): _* )

    val newFormula = apply( formula, variableSubstitution )

    quantifier( newQuantifiedVariables, apply( newFormula, newSubstitution ) )
  }

  /**
   * Substitutes a name by a given expression.
   *
   * @param cas The expression in which the substitution is to be carried out.
   * @param substitution The substitution that is to be applied to the
   * case statement
   * @return An expression that is equivalent to expr[oldName/replacement].
   */
  private def substCase(
    cas:          TipSmtCase,
    substitution: Substitution ): TipSmtCase = {
    val TipSmtConstructorPattern( constructor, boundVariables ) = cas.pattern

    val newSubstitution: Substitution = substitution.filter {
      case ( identifier, _ ) => !boundVariables.contains( identifier )
    }

    val substFreeVars: Set[String] =
      newSubstitution.values.flatMap { freeVariables( problem, _ ) } toSet

    val nameGenerator =
      new NameGenerator(
        substFreeVars ++
          newSubstitution.keys.map { _.name } ++
          freeVariables( problem, cas.expr ) )

    val newBoundVariables = boundVariables map {
      boundName =>
        if ( substFreeVars.contains( boundName.name ) )
          TipSmtIdentifier( nameGenerator.fresh( boundName.name ) )
        else
          boundName
    }

    val variableSubstitution: Substitution = Map(
      boundVariables zip newBoundVariables: _* )

    val newExpr = apply( cas.expr, variableSubstitution )

    TipSmtCase(
      TipSmtConstructorPattern( constructor, newBoundVariables ),
      apply( newExpr, newSubstitution ) )
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
    val newExpression =
      apply(
        tipSmtCase.expr,
        Map(
          oldNames
            .map { TipSmtIdentifier }
            .zip( newBoundNames map { TipSmtIdentifier } ): _* ) )
    TipSmtCase( newPattern, newExpression )
  }
}