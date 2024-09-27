package gapt.formats.tip.decoration

import gapt.formats.tip.analysis.SymbolTable
import gapt.formats.tip.parser.Datatype
import gapt.formats.tip.parser.TipSmtAnd
import gapt.formats.tip.parser.TipSmtAssertion
import gapt.formats.tip.parser.TipSmtCase
import gapt.formats.tip.parser.TipSmtConstructorPattern
import gapt.formats.tip.parser.TipSmtDefault
import gapt.formats.tip.parser.TipSmtDistinct
import gapt.formats.tip.parser.TipSmtEq
import gapt.formats.tip.parser.TipSmtExists
import gapt.formats.tip.parser.TipSmtExpression
import gapt.formats.tip.parser.TipSmtFalse
import gapt.formats.tip.parser.TipSmtForall
import gapt.formats.tip.parser.TipSmtFormalParameter
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
import gapt.formats.tip.parser.TipSmtTrue

class ReconstructDatatypes(problem: TipSmtProblem) {

  problem.symbolTable = Some(new SymbolTable(problem))

  def apply(): TipSmtProblem = {

    problem.definitions foreach {
      case fun @ TipSmtFunctionDefinition(_, _, _, _, _) =>
        apply(fun)
      case funDefs @ TipSmtMutualRecursiveFunctionDefinition(_) =>
        funDefs.functions.foreach { apply }
      case TipSmtAssertion(_, expression) =>
        reconstructTypes(expression, Map())
      case TipSmtGoal(_, expression) =>
        reconstructTypes(expression, Map())
      case _ =>
    }
    problem
  }

  private def apply(fun: TipSmtFunctionDefinition): Unit = {
    val context = fun.parameters map {
      case TipSmtFormalParameter(name, typ) =>
        name -> Datatype(typ.typename)
    }
    reconstructTypes(fun.body, Map(context: _*))
  }

  private def reconstructTypes(
      expression: TipSmtExpression,
      variables: Map[String, Datatype]
  ): Unit = expression match {
    case TipSmtAnd(subexpressions) =>
      subexpressions foreach { reconstructTypes(_, variables) }
      expression.datatype = Some(Datatype("bool"))
    case TipSmtOr(subexpressions) =>
      subexpressions foreach { reconstructTypes(_, variables) }
      expression.datatype = Some(Datatype("bool"))
    case TipSmtImp(subexpressions) =>
      subexpressions foreach { reconstructTypes(_, variables) }
      expression.datatype = Some(Datatype("bool"))
    case TipSmtNot(subexpression) =>
      reconstructTypes(subexpression, variables)
      expression.datatype = Some(Datatype("bool"))
    case TipSmtForall(vars, subexpression) =>
      val context: Seq[(String, Datatype)] = vars map {
        v =>
          v.name -> Datatype(v.typ.typename)
      }
      reconstructTypes(
        subexpression,
        Map(context: _*) ++ variables
      )
      expression.datatype = Some(Datatype("bool"))

    case TipSmtExists(vars, subexpression) =>
      val context: Seq[(String, Datatype)] = vars map {
        v =>
          v.name -> Datatype(v.typ.typename)
      }
      reconstructTypes(
        subexpression,
        Map(context: _*) ++ variables
      )
      expression.datatype = Some(Datatype("bool"))

    case TipSmtIdentifier(identifier) =>
      expression.datatype = Some(variables
        .getOrElse(identifier, problem.symbolTable.get.typeOf(identifier).returnType))

    case TipSmtFun(functionName, arguments) =>
      arguments foreach { arg => reconstructTypes(arg, variables) }
      expression.datatype = Some(
        problem.symbolTable.get.typeOf(functionName).returnType
      )

    case TipSmtTrue =>
      expression.datatype = Some(Datatype("bool"))

    case TipSmtFalse =>
      expression.datatype = Some(Datatype("bool"))

    case TipSmtIte(expr1, expr2, expr3) =>
      reconstructTypes(expr1, variables)
      reconstructTypes(expr2, variables)
      reconstructTypes(expr3, variables)
      expression.datatype = expr2.datatype

    case TipSmtEq(subexpressions) =>
      subexpressions foreach { reconstructTypes(_, variables) }
      expression.datatype = Some(Datatype("bool"))

    case TipSmtMatch(expr, cases) =>
      reconstructTypes(expr, variables)
      cases foreach {
        reconstructTypesCase(expr.datatype.get, _, variables)
      }
      expression.datatype = cases.head.expr.datatype

    case TipSmtDistinct(expressions) =>
      expressions.foreach { reconstructTypes(_, variables) }
      expression.datatype = Some(Datatype("bool"))
  }

  private def reconstructTypesCase(
      matchedType: Datatype,
      tipSmtCase: TipSmtCase,
      variables: Map[String, Datatype]
  ): Unit = {
    tipSmtCase.pattern match {
      case TipSmtDefault =>
        reconstructTypes(tipSmtCase.expr, variables)
      case TipSmtConstructorPattern(constructor, identifiers) =>
        val constructorType = problem.symbolTable.get.typeOf(constructor.name)
        val matchVariables = identifiers.zipWithIndex.filter {
          case (identifier, _) =>
            !problem.symbolTable.get.contains(identifier.name)
        }
        val context = matchVariables map {
          case (identifier, index) =>
            (identifier.name, constructorType.argumentTypes(index))
        }
        reconstructTypes(
          tipSmtCase.expr,
          Map(context: _*) ++ variables
        )
    }
  }
}
