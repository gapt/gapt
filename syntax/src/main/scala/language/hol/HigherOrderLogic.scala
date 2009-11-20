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

    trait Formula extends LambdaExpression {
        require(exptype == To())
        def and(that: Formula) =  And(this, that)
        def or(that: Formula) = Or(this, that)
        def imp(that: Formula) = Imp(this, that)
    }
    trait Const
    trait HOL

    type HOLFormula = HOLTerm with Formula
    type HOLTerm = LambdaExpression with HOL

    class HOLVar private[HigherOrderLogic] (name: VariableSymbolA, exptype: TA)
      extends Var(name, exptype, HOLFactory) with HOL
    class HOLConst private[HigherOrderLogic] (name: ConstantSymbolA, exptype: TA)
      extends Var(name, exptype, HOLFactory) with Const with HOL
    class HOLVarFormula private[HigherOrderLogic] (name: VariableSymbolA)
      extends HOLVar(name, To()) with Formula
    class HOLConstFormula private[HigherOrderLogic] (name: ConstantSymbolA)
      extends HOLConst(name, To()) with Formula
    private[HigherOrderLogic] class HOLApp(function: LambdaExpression, argument: LambdaExpression)
      extends App(function, argument, HOLFactory) with HOL
    class HOLAppFormula private[HigherOrderLogic] (function: LambdaExpression, argument: LambdaExpression)
      extends HOLApp(function, argument) with Formula
    private[HigherOrderLogic] class HOLAbs(variable: Var, expression: LambdaExpression)
      extends Abs(variable, expression, HOLFactory) with HOL

    object HOLVar {
        def apply(name: VariableSymbolA, exptype: TA) = new HOLVar(name, exptype)
    }
    object HOLConst {
        def apply(name: ConstantSymbolA, exptype: TA) = new HOLConst(name, exptype)
    }
    object HOLVarFormula {
        def apply(name: VariableSymbolA) = new HOLVarFormula(name)
    }
    object HOLConstFormula {
        def apply(name: ConstantSymbolA) = new HOLConstFormula(name)
    }
    object HOLAppFormula {
        def apply(function: LambdaExpression, argument: LambdaExpression) = new HOLAppFormula(function, argument)
    }

    val negC = new HOLConst(NegSymbol, "(o -> o)")
    val andC = new HOLConst(AndSymbol, "(o -> (o -> o))")
    val orC  = new HOLConst(OrSymbol, "(o -> (o -> o))")
    val impC = new HOLConst(ImpSymbol, "(o -> (o -> o))")
    def exQ(exptype:TA) = new HOLConst(ExistsSymbol, ->(exptype,"o"))
    def allQ(exptype:TA) = new HOLConst(ForallSymbol, ->(exptype,"o"))

    def isFormula(typ: TA) = typ match {
        case To() => true
        case _ => false
    }

    def isFormulaWhenApplied(typ: TA) = typ match {
        case ->(in,To()) => true
        case _        => false
    }

    object HOLFactory extends LambdaFactoryA {
        def createVar( name: SymbolA, exptype: TA ) : Var =
            name match {
                case a: ConstantSymbolA =>
                    if (isFormula(exptype)) new HOLConstFormula(a)
                    else new HOLConst(a, exptype)
                case a: VariableSymbolA =>
                    if (isFormula(exptype)) new HOLVarFormula(a)
                    else new HOLVar(a, exptype)
            }
        def createApp( fun: LambdaExpression, arg: LambdaExpression ) : App =
            if (isFormulaWhenApplied(fun.exptype)) new HOLAppFormula(fun, arg)
            else new HOLApp(fun, arg)
        def createAbs( variable: Var, exp: LambdaExpression ) : Abs  = new HOLAbs( variable, exp )
    }

    def hol = HOLFactory

    implicit def lambdaToHOL(exp: LambdaExpression): HOLTerm = exp.asInstanceOf[HOLTerm]
    implicit def listLambdaToListHOL(l: List[LambdaExpression]): List[HOLTerm] = l.asInstanceOf[List[HOLTerm]]

      // We do in all of them additional casting into Formula as Formula is a static type and the only way to deynamically express it is via casting.
    object Neg {
        def apply(sub: Formula) = App(negC,sub).asInstanceOf[HOLFormula]
        def unapply(expression: LambdaExpression) = expression match {
            case App(negC,sub) => Some( (sub.asInstanceOf[HOLFormula]) )
            case _ => None
        }
    }

    object And {
        def apply(left: Formula, right: Formula) = (App(App(andC,left),right)).asInstanceOf[HOLFormula]
        def unapply(expression: LambdaExpression) = expression match {
            case App(App(andC,left),right) => Some( (left.asInstanceOf[HOLFormula],right.asInstanceOf[HOLFormula]) )
            case _ => None
        }
    }

    object Or {
        def apply(left: Formula, right: Formula) = App(App(orC,left),right).asInstanceOf[HOLFormula]
        def unapply(expression: LambdaExpression) = expression match {
            case App(App(orC,left),right) => Some( (left.asInstanceOf[Formula],right.asInstanceOf[HOLFormula]) )
            case _ => None
        }
    }

    object Imp {
        def apply(left: Formula, right: Formula) = App(App(impC,left),right).asInstanceOf[HOLFormula]
        def unapply(expression: LambdaExpression) = expression match {
            case App(App(impC,left),right) => Some( (left.asInstanceOf[Formula],right.asInstanceOf[HOLFormula]) )
            case _ => None
        }
    }

    object Ex {
        def apply(sub: LambdaExpression) = App(exQ(sub.exptype),sub).asInstanceOf[HOLFormula]
        def unapply(expression: LambdaExpression) = expression match {
            case App(Var(exS, ->(t,To())),sub) => Some( (sub) )
            case _ => None
        }
    }

    object All {
        def apply(sub: LambdaExpression) = App(allQ(sub.exptype),sub).asInstanceOf[HOLFormula]
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

      // HOL formulas of the form P(t_1,...,t_n)
    object Atom {
        def apply( sym: SymbolA, args: List[HOLTerm]) = {
            val pred : Var = HOLFactory.createVar( sym, FunctionType( To(), args.map( a => a.exptype ) ) )
            AppN(pred, args).asInstanceOf[HOLFormula]
        }
        def unapply( expression: LambdaExpression ) = expression match {
              case Neg(_) => None
              case Or(_, _) => None
              case Imp(_, _) => None
              case Ex(_) => None
              case All(_) => None
              case AppN( Var( name, t ), args )
                if t == FunctionType( To(), args.map( a => a.exptype ) ) => Some( ( name, args ) )
              case _ => None
        }
    }
}
