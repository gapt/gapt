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
  class ExQ protected[quantifiers](e:TA) extends HOLConst(ExistsSymbol, ->(e,"o"))
  class AllQ protected[quantifiers](e:TA) extends HOLConst(ForallSymbol, ->(e,"o"))
  object ExQ {
    def unapply(v: Var) = v match {
      case vo: ExQ => Some(vo.exptype)
      case _ => None
    }
  }
  object AllQ {
    def unapply(v: Var) = v match {
      case vo: AllQ => Some(vo.exptype)
      case _ => None
    }
  }

  object Ex {
    def apply(sub: LambdaExpression) = App(new ExQ(sub.exptype),sub).asInstanceOf[HOLFormula]
    def unapply(expression: LambdaExpression) = expression match {
      case App(ExQ(t),sub) => Some( (sub, t) )
      case _ => None
    }
  }

  object All {
    def apply(sub: LambdaExpression) = App(new AllQ(sub.exptype),sub).asInstanceOf[HOLFormula]
    def unapply(expression: LambdaExpression) = expression match {
      case App(AllQ(t),sub) => Some( (sub, t) )
      case _ => None
    }
  }

  object ExVar {
    def apply(variable: Var, sub: Formula) = Ex(Abs(variable, sub))
    def unapply(expression: LambdaExpression) = expression match {
      case Ex(Abs(variable, sub), _) => Some( (variable, sub.asInstanceOf[HOLFormula]) )
      case _ => None
    }
  }

  object AllVar {
    def apply(variable: Var, sub: Formula) = All(Abs(variable, sub))
    def unapply(expression: LambdaExpression) = expression match {
      case All(Abs(variable, sub), _) => Some( (variable, sub.asInstanceOf[HOLFormula]) )
      case _ => None
    }
  }

  object Quantifier {
    def unapply(expression: LambdaExpression) = expression match {
      case ExVar(x, f) => Some(ExistsSymbol, x, f)
      case AllVar(x, f) => Some(ForallSymbol, x, f)
      case _ => None
    }
  }
}
