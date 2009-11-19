package at.logic.language.lambdatry

import at.logic.language.lambda.Symbols._
import at.logic.language.lambda.Symbols.SymbolImplicitConverters._
import scala.collection.immutable._
import at.logic.language.lambda.Types._
import at.logic.language.hol.LogicSymbols._

object TypedLambdaCalculus {
  // Set the language globally
  object ExpressionFactory {
    var factory : LambdaFactoryA = LambdaFactory
  }

  //
  // TYPED LAMBDA CALCULUS
  //

  trait LambdaExpression {
    def exptype: TA
  }

  trait LambdaFactoryA {
    def createVar( name: SymbolA, exptype: TA ) : Var
    def createAbs( variable: Var, exp: LambdaExpression ) : Abs
    def createApp( fun: LambdaExpression, arg: LambdaExpression ) : App
  }

  object LambdaFactory extends LambdaFactoryA {
    def createVar( name: SymbolA, exptype: TA ) : Var = new Var( name, exptype )
    def createAbs( variable: Var, exp: LambdaExpression ) : Abs = new Abs( variable, exp )
    def createApp( fun: LambdaExpression, arg: LambdaExpression ) : App = new App( fun, arg )
  }

  class Var( val name: SymbolA, val exptype: TA ) extends LambdaExpression

  object Var {
    def apply(name: SymbolA, exptype: TA) = ExpressionFactory.factory.createVar(name, exptype)
    def unapply(expression: LambdaExpression) = expression match {
      case a: Var => Some((a.name, a.exptype))
      case _ => None
    }
  }

  class Abs( val variable: Var, val expression: LambdaExpression ) extends LambdaExpression  {
    def exptype: TA = ->(variable.exptype,expression.exptype)
  }

  object Abs {
    def apply(variable: Var, expression: LambdaExpression) = ExpressionFactory.factory.createAbs(variable, expression)
    def unapply(expression: LambdaExpression) = expression match {
      case a: Abs => Some((a.variable, a.expression))
      case _ => None
    }
  }

  class App( val function: LambdaExpression, val argument: LambdaExpression) extends LambdaExpression {
    require({
      function.exptype match {
        case ->(in,out) => {if (in == argument.exptype) true
          else false}
        case _          => false
      }
    })
    def exptype: TA = {
      function.exptype match {
        case ->(in,out) => out
      }
    }
  }

  object App {
    def apply(function: LambdaExpression, argument: LambdaExpression) = ExpressionFactory.factory.createApp( function, argument )
    def unapply(expression: LambdaExpression) = expression match {
        case a: App => Some((a.function, a.argument))
        case _ => None
    }
  }

  object AppN {
    def apply(function: LambdaExpression, arguments:List[LambdaExpression]): LambdaExpression = arguments match {
        case Nil => function
        case x::ls => apply(App(function, x), ls)
    }
    def unapply(expression: LambdaExpression):Option[(LambdaExpression, List[LambdaExpression])] = Some(unapplyRec(expression))
    def unapplyRec(expression: LambdaExpression):(LambdaExpression, List[LambdaExpression]) = expression match {
        case App(f, arg) => {val t = unapplyRec(f); (t._1, t._2 ::: (arg::Nil)) }
        case v: Var => (v,Nil)
        case a: Abs => (a,Nil)
    }
  }

  //
  // HIGHER ORDER LOGIC
  //

  trait Formula
  trait Const

  type HOLFormula = LambdaExpression with Formula

  class HOLConst(name: ConstantSymbolA, exptype: TA) extends Var(name, exptype) with Const
  class HOLVarFormula(name: VariableSymbolA) extends Var(name, To()) with Formula
  class HOLConstFormula(name: ConstantSymbolA) extends HOLConst(name, To()) with Formula
  class HOLAppFormula(function: LambdaExpression, argument: LambdaExpression) extends App(function, argument) with Formula

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
          else new Var(a, exptype)
    }
    def createApp( fun: LambdaExpression, arg: LambdaExpression ) : App = 
      if (isFormulaWhenApplied(fun.exptype)) new HOLAppFormula(fun, arg)
      else new App(fun, arg)
    def createAbs( variable: Var, exp: LambdaExpression ) = LambdaFactory.createAbs( variable, exp )
  }

  // HOL formulas of the form P(t_1,...,t_n)
  object Atom {
    def apply( sym: SymbolA, args: List[LambdaExpression]) = {
      val pred : Var = new Var( sym, FunctionType( To(), args.map( a => a.exptype ) ) )
      AppN(pred, args).asInstanceOf[HOLFormula]
    }
    /*
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
    */
  }
}
