/*
 * LogicExpressions.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.hol

import at.logic.language.lambda.Symbols._
import LogicSymbols._
import at.logic.language.lambda.TypedLambdaCalculus._
import at.logic.language.lambda.Types._
import at.logic.language.lambda.Types.TAImplicitConverters._
import at.logic.language.lambda.TypedLambdaCalculus._

object HigherOrderLogic {

    trait Const

    implicit object HOLVarFactory extends VarFactory[HOL] {
        def create (name: SymbolA, exptype: TA) = name match {
            case a: ConstantSymbolA => 
                if (isFormula(exptype)) new Var[HOL](name, exptype) with Const with Formula
                else new Var[HOL](name, exptype) with Const
            case _ => 
                if (isFormula(exptype)) new Var[HOL](name, exptype) with Formula
                else new Var[HOL](name, exptype)
        }
    }

    val negC = Var[HOL](NegSymbol, "(o -> o)")
    val andC = Var[HOL](AndSymbol, "(o -> (o -> o))")
    val orC  = Var[HOL](OrSymbol, "(o -> (o -> o))")
    val impC = Var[HOL](ImpSymbol, "(o -> (o -> o))")
    def exQ(exptype:TA) = Var[HOL](ExistsSymbol, ->(exptype,"o"))
    def allQ(exptype:TA) = Var[HOL](ForallSymbol, ->(exptype,"o"))

    trait HOL extends Lambda
    
    trait Formula {
        this: LambdaExpression[HOL] =>
        def and(that: LambdaExpression[HOL] with Formula) =  And(this, that)
        def or(that: LambdaExpression[HOL] with Formula) = Or(this, that)
        def imp(that: LambdaExpression[HOL] with Formula) = Imp(this, that)
    }

    def isFormula(typ: TA) = typ match {
        case To() => true
        case _ => false
    }
    def isFormulaWhenApplied(typ: TA) = typ match {
        case ->(in,o) => true
        case _        => false
    }

    // As I need to know the type of the App before I create it, I check the return type of the function to be o to determine if it is a formula.
    // The validity of the applicaton is tested in the App class
    implicit object HOLAppFactory extends AppFactory[HOL] {
        def create (function: LambdaExpression[HOL], argument: LambdaExpression[HOL]) = 
            if (isFormulaWhenApplied(function.exptype)) new App[HOL](function, argument) with Formula
            else new App[HOL](function, argument)
    }
    implicit object HOLAbsFactory extends AbsFactory[HOL] {
        def create (variable: Var[HOL], expression: LambdaExpression[HOL]) = new Abs[HOL](variable, expression)
    }

    // We do in all of them additional casting into Formula as Formula is a static type and the only way to deynamically express it is via casting.
    object Neg {
        def apply(sub: LambdaExpression[HOL] with Formula) = App(negC,sub).asInstanceOf[App[HOL] with Formula]
        def unapply(expression: LambdaExpression[HOL]) = expression match {
            case App(negC,sub) => Some( (sub) )
            case _ => None
        }
    }

    object And {
        def apply(left: LambdaExpression[HOL] with Formula, right: LambdaExpression[HOL] with Formula) = App(App(andC,left),right).asInstanceOf[App[HOL] with Formula]
        def unapply(expression: LambdaExpression[HOL]) = expression match {
            case App(App(andC,left),right) => Some( (left,right) )
            case _ => None
        }
    }

    object Or {
        def apply(left: LambdaExpression[HOL] with Formula, right: LambdaExpression[HOL] with Formula) = App(App(orC,left),right).asInstanceOf[App[HOL] with Formula]
        def unapply(expression: LambdaExpression[HOL]) = expression match {
            case App(App(orC,left),right) => Some( (left,right) )
            case _ => None
        }
    }

    object Imp {
        def apply(left: LambdaExpression[HOL] with Formula, right: LambdaExpression[HOL] with Formula) = App(App(impC,left),right).asInstanceOf[App[HOL] with Formula]
        def unapply(expression: LambdaExpression[HOL]) = expression match {
            case App(App(impC,left),right) => Some( (left,right) )
            case _ => None
        }
    }

    object Ex {
        def apply(sub: LambdaExpression[HOL]) = App(exQ(sub.exptype),sub).asInstanceOf[App[HOL] with Formula]
        def unapply(expression: LambdaExpression[HOL]) = expression match {
            case App(Var(exS, ->(t,To())),sub) => Some( (sub) )
            case _ => None
        }
    }

    object All {
        def apply(sub: LambdaExpression[HOL]) = App(allQ(sub.exptype),sub).asInstanceOf[App[HOL] with Formula]
        def unapply(expression: LambdaExpression[HOL]) = expression match {
            case App(Var(allS, ->(t,To())),sub) => Some( (sub) )
            case _ => None
        }
    }

    object ExVar {
        def apply(variable: Var[HOL], sub: LambdaExpression[HOL] with Formula) = Ex(Abs(variable, sub))
        def unapply(expression: LambdaExpression[HOL]) = expression match {
            case Ex(Abs(variable, sub)) => Some( (variable, sub) )
            case _ => None
        }
    }

    object AllVar {
        def apply(variable: Var[HOL], sub: LambdaExpression[HOL] with Formula) = All(Abs(variable, sub))
        def unapply(expression: LambdaExpression[HOL]) = expression match {
            case All(Abs(variable, sub)) => Some( (variable, sub) )
            case _ => None
        }
    }
}
