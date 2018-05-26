package gapt.formats.tip.transformation

import gapt.formats.tip.parser.TipSmtAnd
import gapt.formats.tip.parser.TipSmtExpression
import gapt.formats.tip.parser.TipSmtForall
import gapt.formats.tip.parser.TipSmtFunctionDefinition
import gapt.formats.tip.parser.TipSmtIte
import gapt.formats.tip.parser.TipSmtMutualRecursiveFunctionDefinition
import gapt.formats.tip.parser.TipSmtProblem

object moveUniversalQuantifiersInwards extends TipSmtProblemTransformation {
  override def transform( problem: TipSmtProblem ): TipSmtProblem =
    new MoveUniversalQuantifiersInwards( problem )()
}

/**
 * This class moves outermost universal quantifiers in function definitions
 * inwards.
 *
 * Universal quantifiers are distributed over conjuncts. This transformation
 * may result in redundant universal quantifiers which can be eliminated in
 * a next step.
 *
 * @param problem The problem whose function definitions are subject to the
 *                transformation described above.
 */
class MoveUniversalQuantifiersInwards( problem: TipSmtProblem ) {

  def apply(): TipSmtProblem = {
    problem.copy( definitions = problem.definitions map {
      case fun @ TipSmtFunctionDefinition( _, _, _, _, _ ) =>
        apply( fun )
      case funDefs @ TipSmtMutualRecursiveFunctionDefinition( _ ) =>
        funDefs.copy( functions = funDefs.functions.map { apply } )
      case definition => definition
    } )
  }

  private def apply(
    fun: TipSmtFunctionDefinition ): TipSmtFunctionDefinition = {
    fun.copy( body = moveUniversalQuantifiersInwards( fun.body ) )
  }

  private def moveUniversalQuantifiersInwards(
    expression: TipSmtExpression ): TipSmtExpression = {
    expression match {
      case expr @ TipSmtAnd( _ ) =>
        moveUniversalQuantifiersInwards( expr )
      case expr @ TipSmtForall( _, _ ) =>
        moveUniversalQuantifiersInwards( expr )
      case expr @ TipSmtIte( _, _, _ ) =>
        moveUniversalQuantifiersInwards( expr )
      case formula => formula
    }
  }

  private def moveUniversalQuantifiersInwards(
    expression: TipSmtAnd ): TipSmtExpression = {
    expression.copy( expression.exprs map { moveUniversalQuantifiersInwards } )
  }

  private def moveUniversalQuantifiersInwards(
    expression: TipSmtIte ): TipSmtExpression = {
    TipSmtIte(
      expression.cond,
      moveUniversalQuantifiersInwards( expression.ifTrue ),
      moveUniversalQuantifiersInwards( expression.ifFalse ) )
  }

  private def moveUniversalQuantifiersInwards(
    expression: TipSmtForall ): TipSmtExpression = {
    expression.formula match {
      case TipSmtAnd( conjuncts ) =>
        TipSmtAnd( conjuncts
          .map { TipSmtForall( expression.variables, _ ) }
          .map { moveUniversalQuantifiersInwards } )
      case _ => expression
    }
  }
}
