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

    private def createHOLApp(function: HOL, argument: LambdaExpression) = if (isFormulaWhenApplied(function.exptype)) new App(function, argument) with HOLFormula else new App(function, argument) with HOL
    implicit object HOLConstHOLAppFactory extends AppFactory[HOLConst] {
        def create (function: HOLConst, argument: LambdaExpression) = createHOLApp(function, argument)
    }
    implicit object HOLVarHOLAppFactory extends AppFactory[HOLVar] {
        def create (function: HOLVar, argument: LambdaExpression) = createHOLApp(function, argument)
    }
    implicit object AppHOLAppFactory extends AppFactory[App with HOL] {
        def create (function: App with HOL, argument: LambdaExpression) = createHOLApp(function, argument)
    }
    implicit object AbsHOLAppFactory extends AppFactory[Abs with HOL] {
        def create (function: Abs with HOL, argument: LambdaExpression) = createHOLApp(function, argument)
    }
    implicit object HOLFormulaAppFactory extends AppFactory[HOLFormula] {
        def create (function: HOLFormula, argument: LambdaExpression) = createHOLApp(function, argument)
    }

    private def createHOLAbs(variable: Var, expression: HOL) = new Abs(variable, expression) with HOL
    implicit object HOLConstHOLAbsFactory extends AbsFactory[HOLConst] {
        def create (variable: Var, expression: HOLConst) = createHOLAbs(variable, expression)
    }
    implicit object HOLVarHOLAbsFactory extends AbsFactory[HOLVar] {
        def create (variable: Var, expression: HOLVar) = createHOLAbs(variable, expression)
    }
    implicit object AppHOLAbsFactory extends AbsFactory[App with HOL] {
        def create (variable: Var, expression: App with HOL) = createHOLAbs(variable, expression)
    }
    implicit object AbsHOLAbsFactory extends AbsFactory[Abs with HOL] {
        def create (variable: Var, expression: Abs with HOL) = createHOLAbs(variable, expression)
    }
    implicit object HOLFormulaAbsFactory extends AbsFactory[HOLFormula] {
        def create (variable: Var, expression: HOLFormula) = createHOLAbs(variable, expression)
    }

    object Neg {
        def apply(sub: HOLFormula) = App(negC,sub)
        def unapply(expression: LambdaExpression) = expression match {
            case App(negC,sub) => Some( (sub) )
            case _ => None
        }
    }

    object And {
        def apply(left: HOLFormula, right: HOLFormula) = App(App(andC,left).asInstanceOf[App with HOL],right)
        def unapply(expression: LambdaExpression) = expression match {
            case App(App(andC,left),right) => Some( (left,right) )
            case _ => None
        }
    }

    object Or {
        def apply(left: HOLFormula, right: HOLFormula) = App(App(orC,left).asInstanceOf[App with HOL],right)
        def unapply(expression: LambdaExpression) = expression match {
            case App(App(orC,left),right) => Some( (left,right) )
            case _ => None
        }
    }

    object Imp {
        def apply(left: HOLFormula, right: HOLFormula) = App(App(impC,left).asInstanceOf[App with HOL],right)
        def unapply(expression: LambdaExpression) = expression match {
            case App(App(impC,left),right) => Some( (left,right) )
            case _ => None
        }
    }

    object Ex {
        def apply(sub: LambdaExpression) = App(exQ(sub.exptype),sub)
        def unapply(expression: LambdaExpression) = expression match {
            case App(Var(exS, ->(t,To())),sub) => Some( (sub) )
            case _ => None
        }
    }

    object All {
        def apply(sub: LambdaExpression) = App(allQ(sub.exptype),sub)
        def unapply(expression: LambdaExpression) = expression match {
            case App(Var(allS, ->(t,To())),sub) => Some( (sub) )
            case _ => None
        }
    }

    object ExVar {
        def apply(variable: Var, sub: HOLFormula) = Ex(Abs(variable, sub))
        def unapply(expression: LambdaExpression) = expression match {
            case Ex(Abs(variable, sub)) => Some( (variable, sub) )
            case _ => None
        }
    }

    object AllVar {
        def apply(variable: Var, sub: HOLFormula) = All(Abs(variable, sub))
        def unapply(expression: LambdaExpression) = expression match {
            case All(Abs(variable, sub)) => Some( (variable, sub) )
            case _ => None
        }
    }
}
