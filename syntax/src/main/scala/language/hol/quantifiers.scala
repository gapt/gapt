/*
 * quantifiers.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.hol

import at.logic.language.lambda.symbols._
import logicSymbols._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.typedLambdaCalculus._
import propositions._
import propositions.TypeSynonyms._

package quantifiers {
  case class ExQ(override val exptype:TA) extends HOLConst(ExistsSymbol, ->(exptype,"o"))
  case class AllQ(override val exptype:TA) extends HOLConst(ForallSymbol, ->(exptype,"o"))

  object Ex {
    def apply(sub: LambdaExpression) = App(ExQ(sub.exptype),sub).asInstanceOf[HOLFormula]
    def unapply(expression: LambdaExpression) = expression match {
      case App(Var(exS, ->(t,To())),sub) => Some( (sub) )
      case _ => None
    }
  }

  object All {
    def apply(sub: LambdaExpression) = App(AllQ(sub.exptype),sub).asInstanceOf[HOLFormula]
    def unapply(expression: LambdaExpression) = expression match {
      case App(Var(allS, ->(t,To())),sub) => Some( (sub) )
      case _ => None
    }
  }

  object ExVar {
    def apply(variable: Var, sub: Formula) = Ex(Abs(variable, sub))
    def unapply(expression: LambdaExpression) = expression match {
      case Ex(Abs(variable, sub)) => Some( (variable, sub.asInstanceOf[Formula]) )
      case _ => None
    }
  }

  object AllVar {
    def apply(variable: Var, sub: Formula) = All(Abs(variable, sub))
    def unapply(expression: LambdaExpression) = expression match {
      case All(Abs(variable, sub)) => Some( (variable, sub.asInstanceOf[Formula]) )
      case _ => None
    }
  }
}
