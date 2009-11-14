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

    type HOLFormula = LambdaExpression[HOL] with Formula[HOL]
    type HOLTerm = LambdaExpression[HOL]
    
    trait Const
    
//    trait FOL extends HOL
//    implicit object FOLVarFactory extends VarFactory[FOL] {
//      def create (name: SymbolA, exptype: TA) = {
//        if exptype != Ti() throw...
//      }

    implicit object HOLVarFactory extends VarFactory[HOL] {
        def create (name: SymbolA, exptype: TA) = name match {
            case a: ConstantSymbolA => 
                if (isFormula(exptype)) new HOLConstFormula(a)
                else new HOLConst(a, exptype)
            case a: VariableSymbolA =>
                if (isFormula(exptype)) new HOLVarFormula(a)
                else new Var[HOL](a, exptype)
        }
    }

    val negC = Var[HOL](NegSymbol, "(o -> o)")
    val andC = Var[HOL](AndSymbol, "(o -> (o -> o))")
    val orC  = Var[HOL](OrSymbol, "(o -> (o -> o))")
    val impC = Var[HOL](ImpSymbol, "(o -> (o -> o))")
    def exQ(exptype:TA) = Var[HOL](ExistsSymbol, ->(exptype,"o"))
    def allQ(exptype:TA) = Var[HOL](ForallSymbol, ->(exptype,"o"))

    trait HOL extends Lambda
    
    trait Formula[+A <: HOL] extends LambdaExpression[A] {
        require(exptype == To())
        def and[B <: HOL](that: LambdaExpression[B] with Formula[B]) =  And(this, that)
        def or[B <: HOL](that: LambdaExpression[B] with Formula[B]) = Or(this, that)
        def imp[B <: HOL](that: LambdaExpression[B] with Formula[B]) = Imp(this, that)
    }

    def isFormula(typ: TA) = typ match {
        case To() => true
        case _ => false
    }
    def isFormulaWhenApplied(typ: TA) = typ match {
        case ->(in,To()) => true
        case _        => false
    }

    // As I need to know the type of the App before I create it, I check the return type of the function to be o to determine if it is a formula.
    // The validity of the applicaton is tested in the App class

    // convenient classes for creating HOL formulas and consts
    //trait HOLFormula extends LambdaExpression[HOL] with Formula[HOL]
    class HOLAppFormula(function: LambdaExpression[HOL], argument: LambdaExpression[HOL]) extends App[HOL](function, argument) with Formula[HOL]
    class HOLVarFormula(name: VariableSymbolA) extends Var[HOL](name, To()) with Formula[HOL]
    class HOLConstFormula(name: ConstantSymbolA) extends Var[HOL](name, To()) with Formula[HOL] with Const
    class HOLConst(name: ConstantSymbolA, exptype: TA) extends Var[HOL](name, exptype) with Const

    implicit object HOLAppFactory extends AppFactory[HOL] {
        def create (function: LambdaExpression[HOL], argument: LambdaExpression[HOL]) = 
            if (isFormulaWhenApplied(function.exptype)) new HOLAppFormula(function, argument)
            else new App[HOL](function, argument)
    }
    implicit object HOLAbsFactory extends AbsFactory[HOL] {
        def create (variable: Var[HOL], expression: LambdaExpression[HOL]) = new Abs[HOL](variable, expression)
    }

    // We do in all of them additional casting into Formula as Formula is a static type and the only way to deynamically express it is via casting.
    object Neg {
        def apply[A <: HOL](sub: LambdaExpression[A] with Formula[A]) = App(negC,sub).asInstanceOf[LambdaExpression[A] with Formula[A]]
        def unapply(expression: LambdaExpression[HOL]) = expression match {
            case App(negC,sub) => Some( (sub) )
            case _ => None
        }
    }

    object And {
        def apply[A <: HOL](left: LambdaExpression[A] with Formula[A], right: LambdaExpression[A] with Formula[A]) = (App(App(andC,left),right)).asInstanceOf[LambdaExpression[A] with Formula[A]]
        def unapply(expression: LambdaExpression[HOL]) = expression match {
            case App(App(andC,left),right) => Some( (left,right) )
            case _ => None
        }
    }

    object Or {
        def apply[A <: HOL](left: LambdaExpression[A] with Formula[A], right: LambdaExpression[A] with Formula[A]) = App(App(orC,left),right).asInstanceOf[LambdaExpression[A] with Formula[A]]
        def unapply(expression: LambdaExpression[HOL]) = expression match {
            case App(App(orC,left),right) => Some( (left,right) )
            case _ => None
        }
    }

    object Imp {
        def apply[A <: HOL](left: LambdaExpression[A] with Formula[A], right: LambdaExpression[A] with Formula[A]) = App(App(impC,left),right).asInstanceOf[LambdaExpression[A] with Formula[A]]
        def unapply(expression: LambdaExpression[HOL]) = expression match {
            case App(App(impC,left),right) => Some( (left,right) )
            case _ => None
        }
    }

    object Ex {
        def apply[A <: HOL](sub: LambdaExpression[A]) = App(exQ(sub.exptype),sub).asInstanceOf[LambdaExpression[A] with Formula[A]]
        def unapply(expression: LambdaExpression[HOL]) = expression match {
            case App(Var(exS, ->(t,To())),sub) => Some( (sub) )
            case _ => None
        }
    }

    object All {
        def apply[A <: HOL](sub: LambdaExpression[A]) = App(allQ(sub.exptype),sub).asInstanceOf[LambdaExpression[A] with Formula[A]]
        def unapply(expression: LambdaExpression[HOL]) = expression match {
            case App(Var(allS, ->(t,To())),sub) => Some( (sub) )
            case _ => None
        }
    }

    object ExVar {
        def apply[A <: HOL](variable: Var[A], sub: LambdaExpression[A] with Formula[A])(implicit factory: AbsFactory[A]) = Ex(Abs(variable, sub))
        def unapply(expression: LambdaExpression[HOL]) = expression match {
            case Ex(Abs(variable, sub)) => Some( (variable, sub) )
            case _ => None
        }
    }

    object AllVar {
        def apply[A <: HOL](variable: Var[A], sub: LambdaExpression[A] with Formula[A])(implicit factory: AbsFactory[A]) = All(Abs(variable, sub))
        def unapply(expression: LambdaExpression[HOL]) = expression match {
            case All(Abs(variable, sub)) => Some( (variable, sub) )
            case _ => None
        }
    }

    // HOL formulas of the form P(t_1,...,t_n)
    // All the factories here are parameterized so they can be used as is (and implicitly) in subclases of HOL
    object Atom {
      def apply[A <: HOL]( sym: SymbolA, args: List[LambdaExpression[A]])(implicit factory1: VarFactory[A], factory2: AppFactory[A]) = {
        val pred = Var[A]( sym, FunctionType( To(), args.map( a => a.exptype ) ) )
        AppN(pred, args).asInstanceOf[LambdaExpression[A] with Formula[A]]
      }
      def unapply( expression: LambdaExpression[HOL] ) = expression match {
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
