package at.logic.gapt.language

import at.logic.gapt.expr._

package object schema {
  type SchemaExpression = LambdaExpression
  type IntegerTerm = LambdaExpression
  type IntVar = Var
  type SchemaFormula = Formula
}
