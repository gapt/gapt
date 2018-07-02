package gapt.formats.tip.transformation

import gapt.formats.tip.analysis.SymbolTable
import gapt.formats.tip.parser.TipSmtAnd
import gapt.formats.tip.parser.TipSmtAssertion
import gapt.formats.tip.parser.TipSmtCase
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
import gapt.formats.tip.util.freeVariables

object eliminateRedundantQuantifiers extends TipSmtProblemTransformation {
  override def transform( problem: TipSmtProblem ): TipSmtProblem =
    new EliminateUselessQuantifiers( problem )()
}

/**
 * This class eliminates useless quantifiers in TIP problems.
 *
 * A quantifier is considered as useless if its bound variable does not occur
 * freely in its formula.
 *
 * @param problem The TIP problem in which useless quantifiers are to be
 *                eliminated.
 */
class EliminateUselessQuantifiers( problem: TipSmtProblem ) {

  problem.symbolTable = Some( SymbolTable( problem ) )

  /**
   * Eliminate useless quantifiers in the entire problem.
   *
   * Quantifiers are eliminated in goals, assertions and the body of function
   * definitions.
   *
   * @return A TIP problem not containing useless quantifiers.
   */
  def apply(): TipSmtProblem = {
    problem.copy( definitions = problem.definitions map {
      case fun @ TipSmtFunctionDefinition( _, _, _, _, _ ) =>
        apply( fun )
      case goal @ TipSmtGoal( _, formula ) =>
        goal.copy( expr = this( formula ) )
      case funDefs @ TipSmtMutualRecursiveFunctionDefinition( _ ) =>
        funDefs.copy( functions = funDefs.functions map { apply } )
      case assertion @ TipSmtAssertion( _, formula ) =>
        assertion.copy( expr = this( formula ) )
      case definition => definition
    } )
  }

  private def apply(
    fun: TipSmtFunctionDefinition ): TipSmtFunctionDefinition = {
    fun.copy( body = this( fun.body ) )
  }

  /**
   * Eliminates useless quantifiers in an expression.
   *
   * @param expression The expression in which useless quantifiers are to be
   *                   eliminated.
   * @return An equivalent expression not containing useless quantifiers.
   */
  def apply( expression: TipSmtExpression ): TipSmtExpression = {
    expression match {
      case expr @ TipSmtAnd( _ ) =>
        expr.copy( expr.exprs.map( this( _ ) ) )
      case expr @ TipSmtImp( _ ) =>
        expr.copy( expr.exprs.map( this( _ ) ) )
      case expr @ TipSmtOr( _ ) =>
        expr.copy( expr.exprs.map( this( _ ) ) )
      case expr @ TipSmtEq( _ ) =>
        expr.copy( expr.exprs.map( this( _ ) ) )
      case TipSmtForall( boundVariables, formula ) =>
        val freeVars = freeVariables( problem, formula )
        val newBoundVariables = boundVariables.filter { v =>
          freeVars.contains( v.name )
        }
        val newFormula = this( formula )
        if ( newBoundVariables.isEmpty ) {
          newFormula
        } else {
          TipSmtForall( newBoundVariables, newFormula )
        }
      case TipSmtExists( boundVariables, formula ) =>
        val freeVars = freeVariables( problem, formula )
        val newBoundVariables = boundVariables.filter { v =>
          freeVars.contains( v.name )
        }
        val newFormula = this( formula )
        if ( newBoundVariables.isEmpty ) {
          newFormula
        } else {
          TipSmtExists( newBoundVariables, newFormula )
        }
      case expr @ TipSmtFun( _, _ ) =>
        expr.copy( arguments = expr.arguments.map( this( _ ) ) )
      case expr @ TipSmtIte( _, _, _ ) =>
        TipSmtIte(
          this( expr.cond ),
          this( expr.ifTrue ),
          this( expr.ifFalse ) )
      case expr @ TipSmtMatch( _, _ ) =>
        expr.copy( cases = expr.cases map { c =>
          TipSmtCase( c.pattern, this( c.expr ) )
        } )
      case expr @ TipSmtNot( _ ) =>
        TipSmtNot( this( expr.expr ) )
      case _ => expression
    }
  }
}

