/*
 * QuantifiedLogicExpressions.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language

import Symbols._
import TypedLambdaCalculus._
import Types._
import Types.TAImplicitConverters._
import LogicExpressions._

object QuantifiedLogicExpressions { // change to "Quantifiers"

    val exS = LatexSymbol("\\exists", "ex")         ; def exQ(exptype:TA) = Var(exS, ->(exptype,"o"))
    val allS = LatexSymbol("\\forall", "all")       ; def allQ(exptype:TA) = Var(allS, ->(exptype,"o"))


    trait QuantifiedLogicExpression extends LogicExpression   //change to "QuantifiedExpression"

    object Ex {
        def apply(sub: LambdaExpression) = new App(exQ(sub.exptype),sub) with QuantifiedLogicExpression
        def unapply(expression: LambdaExpression) = expression match {
            case App(Var(exS, ->(t,To())),sub) => if (sub.exptype == t) Some( (sub) ) else None
            case _ => None
        }
    }

    object All {
        def apply(sub: LambdaExpression) = new App(allQ(sub.exptype),sub) with QuantifiedLogicExpression
        def unapply(expression: LambdaExpression) = expression match {
            case App(Var(allS, ->(t,To())),sub) => if (sub.exptype == t) Some( (sub) ) else None
            case _ => None
        }
    }

    object ExVar {
        def apply(variable: Var, sub: LambdaExpression) = Ex(Abs(variable, sub))
        def unapply(expression: LambdaExpression) = expression match {
            case Ex(Abs(variable, sub)) => Some( (variable, sub) )
            case _ => None
        }
    }

    object AllVar {
        def apply(variable: Var, sub: LambdaExpression) = All(Abs(variable, sub))
        def unapply(expression: LambdaExpression) = expression match {
            case All(Abs(variable, sub)) => Some( (variable, sub) )
            case _ => None
        }
    }

}
