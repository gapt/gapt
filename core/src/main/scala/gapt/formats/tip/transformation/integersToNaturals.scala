package gapt.formats.tip.transformation

import gapt.formats.tip.parser.TipSmtAnd
import gapt.formats.tip.parser.TipSmtAssertion
import gapt.formats.tip.parser.TipSmtCommand
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
import gapt.formats.tip.parser.TipSmtNot
import gapt.formats.tip.parser.TipSmtOr
import gapt.formats.tip.parser.TipSmtProblem

object integersToNaturals extends TipSmtProblemTransformation {
  override def transform(problem: TipSmtProblem): TipSmtProblem =
    new IntegerToNaturalConversion(problem)()
}

class IntegerToNaturalConversion(problem: TipSmtProblem) {

  def apply(): TipSmtProblem = {
    problem.copy(definitions = problem.definitions map {
      integersToNaturalsDefinitionVisitor.dispatch(_, ())
    })
  }

  private object integersToNaturalsDefinitionVisitor
      extends TipSmtDefinitionTransformation[Unit] {

    override def visit(
        definition: TipSmtFunctionDefinition,
        data: Unit
    ): TipSmtCommand =
      apply(definition)

    override def visit(
        definitions: TipSmtMutualRecursiveFunctionDefinition,
        data: Unit
    ): TipSmtCommand =
      definitions.copy(functions = definitions.functions.map { apply })

    override def visit(
        goal: TipSmtGoal,
        data: Unit
    ): TipSmtCommand =
      goal.copy(expr = convertIntegersToNaturals(goal.expr))

    override def visit(
        assertion: TipSmtAssertion,
        data: Unit
    ): TipSmtCommand =
      assertion.copy(expr = convertIntegersToNaturals(assertion.expr))
  }

  private def convertIntegersToNaturals(expression: TipSmtExpression): TipSmtExpression = {
    expression match {
      case expr @ TipSmtAnd(es) =>
        TipSmtAnd(es map { convertIntegersToNaturals(_) })
      case expr @ TipSmtOr(es) =>
        TipSmtOr(es map { convertIntegersToNaturals(_) })
      case expr @ TipSmtImp(es) =>
        TipSmtImp(es map { convertIntegersToNaturals(_) })
      case expr @ TipSmtForall(vs, f) =>
        TipSmtForall(vs, convertIntegersToNaturals(f))
      case expr @ TipSmtExists(vs, f) =>
        TipSmtExists(vs, convertIntegersToNaturals(f))
      case expr @ TipSmtIte(cond, ifTrue, ifFalse) =>
        TipSmtIte(
          convertIntegersToNaturals(cond),
          convertIntegersToNaturals(ifTrue),
          convertIntegersToNaturals(ifFalse)
        )
      case expr @ TipSmtEq(es) =>
        TipSmtEq(es map { convertIntegersToNaturals })
      case expr @ TipSmtFun(f, as) =>
        TipSmtFun(f, as map { convertIntegersToNaturals })
      case expr @ TipSmtNot(f) =>
        TipSmtNot(convertIntegersToNaturals(f))
      case expr @ TipSmtMatch(e, cases) =>
        TipSmtMatch(
          convertIntegersToNaturals(e),
          cases map { c => c.copy(expr = convertIntegersToNaturals(c.expr)) }
        )
      case TipSmtIdentifier(n) if n.matches("[0-9][0-9]*") =>
        numeral(n.toInt)
      case e => e
    }
  }

  private def numeral(n: Int): TipSmtExpression = {
    if (n == 0)
      TipSmtIdentifier("zero")
    else
      TipSmtFun("succ", Seq(numeral(n - 1)))
  }

  private def apply(
      fun: TipSmtFunctionDefinition
  ): TipSmtFunctionDefinition = {
    fun.copy(body = convertIntegersToNaturals(fun.body))
  }

}
