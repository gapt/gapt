package at.logic.language.lambdatry

import at.logic.language.lambda.Symbols._
import at.logic.language.lambda.Symbols.SymbolImplicitConverters._
import scala.collection.immutable._
import at.logic.language.lambda.Types._
import at.logic.language.hol.LogicSymbols._

object TypedLambdaCalculus {

  //
  // TYPED LAMBDA CALCULUS
  //

  trait LambdaExpression {
    def exptype: TA
    private[TypedLambdaCalculus] val factory: LambdaFactoryA
  }

  trait LambdaFactoryA {
    def createVar( name: SymbolA, exptype: TA ) : Var
    def createAbs( variable: Var, exp: LambdaExpression ) : Abs
    def createApp( fun: LambdaExpression, arg: LambdaExpression ) : App
  }

  object LambdaFactory extends LambdaFactoryA {
    def createVar( name: SymbolA, exptype: TA ) : Var = new Var( name, exptype, this )
    def createAbs( variable: Var, exp: LambdaExpression ) : Abs = new Abs( variable, exp, this )
    def createApp( fun: LambdaExpression, arg: LambdaExpression ) : App = new App( fun, arg, this )
  }

  class Var private[TypedLambdaCalculus]( val name: SymbolA, val exptype: TA, val factory: LambdaFactoryA) extends LambdaExpression

  object Var {
    def apply(name: SymbolA, exptype: TA, factory: LambdaFactoryA) = factory.createVar(name, exptype)
    def unapply(expression: LambdaExpression) = expression match {
      case a: Var => Some((a.name, a.exptype))
      case _ => None
    }
  }

  class Abs private[TypedLambdaCalculus]( val variable: Var, val expression: LambdaExpression, val factory: LambdaFactoryA ) extends LambdaExpression  {
    def exptype: TA = ->(variable.exptype,expression.exptype)
  }

  object Abs {
    def apply(variable: Var, expression: LambdaExpression) = expression.factory.createAbs(variable, expression)
    def unapply(expression: LambdaExpression) = expression match {
      case a: Abs => Some((a.variable, a.expression))
      case _ => None
    }
  }

  class App private[TypedLambdaCalculus]( val function: LambdaExpression, val argument: LambdaExpression, val factory: LambdaFactoryA) extends LambdaExpression {
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
    def apply(function: LambdaExpression, argument: LambdaExpression) = function.factory.createApp( function, argument )
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
  trait HOL

  type HOLFormula = LambdaExpression with Formula with HOL
  type HOLTerm = LambdaExpression with HOL

  private class HOLVar(name: VariableSymbolA, exptype: TA) extends Var(name, exptype, HOLFactory) with HOL
  private class HOLConst(name: ConstantSymbolA, exptype: TA) extends Var(name, exptype, HOLFactory) with Const with HOL
  private class HOLVarFormula(name: VariableSymbolA) extends Var(name, To(), HOLFactory) with Formula with HOL
  private class HOLConstFormula(name: ConstantSymbolA) extends HOLConst(name, To()) with Formula with HOL
  private class HOLAppFormula(function: LambdaExpression, argument: LambdaExpression) extends App(function, argument, HOLFactory) with Formula with HOL
  private class HOLApp(function: LambdaExpression, argument: LambdaExpression) extends App(function, argument, HOLFactory) with Formula with HOL
  private class HOLAbs(variable: Var, expression: LambdaExpression) extends Abs(variable, expression, HOLFactory) with HOL

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

  // HOL formulas of the form P(t_1,...,t_n)
  object Atom {
    def apply( sym: SymbolA, args: List[HOLTerm]) = {
      val pred : Var = HOLFactory.createVar( sym, FunctionType( To(), args.map( a => a.exptype ) ) )
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
