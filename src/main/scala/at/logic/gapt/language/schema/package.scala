package at.logic.gapt.language

import at.logic.gapt.expr._

package object schema {
  type SchemaExpression = LambdaExpression
  type IntegerTerm = LambdaExpression
  type IntConst = Const
  type SchemaFormula = Formula
  type fo2Var = Var
  type IntVar = Var
}

