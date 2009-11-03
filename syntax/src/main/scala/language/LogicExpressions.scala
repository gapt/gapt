/*
 * LogicExpressions.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language

import Symbols._
import LogicSymbols._
import TypedLambdaCalculus._
import Types._
import Types.TAImplicitConverters._
import TypedLambdaCalculus._

object HigherOrderLogic {  // change file to "HigherOrderLogic"

    val negC = HOLConst(NegSymbol, "(o -> o)")
    val andC = HOLConst(AndSymbol, "(o -> (o -> o))")
    val orC  = HOLConst(OrSymbol, "(o -> (o -> o))")
    val impC = HOLConst(ImpSymbol, "(o -> (o -> o))")
    def exQ(exptype:TA) = HOLConst(ExistsSymbol, ->(exptype,"o"))
    def allQ(exptype:TA) = HOLConst(ForallSymbol, ->(exptype,"o"))

    trait HOL extends LambdaExpression
    
    trait HOLFormula extends HOL {
        def and(that: HOLFormula) =  And(this, that)
        def or(that: HOLFormula) = Or(this, that)
        def imp(that: HOLFormula) = Imp(this, that)
    }

    def isFormula(typ: TA) = typ match {
        case To() => true
        case _ => false
    }
    def isFormulaWhenApplied(typ: TA) = typ match {
        case ->(in,o) => true
        case _        => false
    }

    class HOLConst private(override val name: ConstantSymbolA, override val exptype: TA) extends Var(name, exptype) with HOL
    object HOLConst {
        def apply(name: ConstantSymbolA, exptype: TA) = if (isFormula(exptype)) new HOLConst(name, exptype) with HOLFormula else new HOLConst(name, exptype)
        def unapply(exp: HOL) = exp match {
            case a: HOLConst => Some((a.name, a.exptype))
            case _ => None
        }
    }

    class HOLVar (override val name: VariableSymbolA, override val exptype: TA) extends Var(name, exptype) with HOL
    object HOLVar {
        def apply(name: VariableSymbolA, exptype: TA) = if (isFormula(exptype)) new HOLVar(name, exptype) with HOLFormula else new HOLVar(name, exptype)
        def unapply(exp: HOL) = exp match {
            case a: HOLVar => Some((a.name, a.exptype))
            case _ => None
        }
    }
    
    implicit object HOLAppFactory extends AppFactory[HOL] {
        def create (function: HOL, argument: LambdaExpression) = if (isFormulaWhenApplied(function.exptype)) new App(function, argument) with HOL with HOLFormula else new App(function, argument) with HOL
    }
    implicit object HOLAbsFactory extends AbsFactory[HOL] {
        def create (variable: Var, expression: HOL) = new Abs(variable, expression) with HOL
    }

    object Neg {
        def apply(sub: HOLFormula) = App[HOL](negC,sub)
        def unapply(expression: LambdaExpression) = expression match {
            case App(negC,sub) => Some( (sub) )
            case _ => None
        }
    }

    object And {
        def apply(left: HOLFormula, right: HOLFormula) = App[HOL](App[HOL](andC,left).asInstanceOf[HOL],right)
        def unapply(expression: LambdaExpression) = expression match {
            case App(App(andC,left),right) => Some( (left,right) )
            case _ => None
        }
    }

    object Or {
        def apply(left: HOLFormula, right: HOLFormula) = App[HOL](App[HOL](orC,left).asInstanceOf[HOL],right)
        def unapply(expression: LambdaExpression) = expression match {
            case App(App(orC,left),right) => Some( (left,right) )
            case _ => None
        }
    }

    object Imp {
        def apply(left: HOLFormula, right: HOLFormula) = App[HOL](App[HOL](impC,left).asInstanceOf[HOL],right)
        def unapply(expression: LambdaExpression) = expression match {
            case App(App(impC,left),right) => Some( (left,right) )
            case _ => None
        }
    }

    object Ex {
        def apply(sub: LambdaExpression) = App[HOL](exQ(sub.exptype),sub)
        def unapply(expression: LambdaExpression) = expression match {
            case App(Var(exS, ->(t,To())),sub) => Some( (sub) )
            case _ => None
        }
    }

    object All {
        def apply(sub: LambdaExpression) = App[HOL](allQ(sub.exptype),sub)
        def unapply(expression: LambdaExpression) = expression match {
            case App(Var(allS, ->(t,To())),sub) => Some( (sub) )
            case _ => None
        }
    }

    object ExVar {
        def apply(variable: Var, sub: HOLFormula) = Ex(Abs[HOL](variable, sub))
        def unapply(expression: LambdaExpression) = expression match {
            case Ex(Abs(variable, sub)) => Some( (variable, sub) )
            case _ => None
        }
    }

    object AllVar {
        def apply(variable: Var, sub: HOLFormula) = All(Abs[HOL](variable, sub))
        def unapply(expression: LambdaExpression) = expression match {
            case All(Abs(variable, sub)) => Some( (variable, sub) )
            case _ => None
        }
    }
}
