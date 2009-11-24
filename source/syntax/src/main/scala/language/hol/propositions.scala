/*
 * LogicExpressions.scala
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

package propositions {

  trait Formula extends LambdaExpression {
    require(exptype == To())
    def and(that: Formula) =  And(this, that)
    def or(that: Formula) = Or(this, that)
    def imp(that: Formula) = Imp(this, that)
  }
  trait Const
  trait HOL extends LambdaFactoryProvider {
    override def factory : LambdaFactoryA = HOLFactory
  }

  object TypeSynonyms {
    type HOLFormula = HOLTerm with Formula
    type HOLTerm = LambdaExpression with HOL
  }

  import TypeSynonyms._
  
  class HOLVar protected[propositions] (name: VariableSymbolA, exptype: TA)
    extends Var(name, exptype) with HOL
  class HOLConst protected[propositions] (name: ConstantSymbolA, exptype: TA)
    extends Var(name, exptype) with Const with HOL
  class HOLVarFormula protected[propositions] (name: VariableSymbolA)
    extends HOLVar(name, To()) with Formula
  class HOLConstFormula protected[propositions] (name: ConstantSymbolA)
    extends HOLConst(name, To()) with Formula
  class HOLApp protected[propositions] (function: LambdaExpression, argument: LambdaExpression)
    extends App(function, argument) with HOL
  class HOLAppFormula protected[propositions] (function: LambdaExpression, argument: LambdaExpression)
    extends HOLApp(function, argument) with Formula
  class HOLAbs protected[propositions] (variable: Var, expression: LambdaExpression)
    extends Abs(variable, expression) with HOL

  object HOLVar {
    def apply(name: VariableSymbolA, exptype: TA) = HOLFactory.createVar(name, exptype).asInstanceOf[HOLVar]
  }
  object HOLConst {
    def apply(name: ConstantSymbolA, exptype: TA) = HOLFactory.createVar(name, exptype).asInstanceOf[HOLConst]
  }
  object HOLVarFormula {
    def apply(name: VariableSymbolA) = HOLFactory.createVar(name, To()).asInstanceOf[HOLVarFormula]
  }
  object HOLConstFormula {
    def apply(name: ConstantSymbolA) = HOLFactory.createVar(name, To()).asInstanceOf[HOLConstFormula]
  }
  object HOLApp {
    def apply(function: LambdaExpression, argument: LambdaExpression) = function.factory.createApp(function, argument).asInstanceOf[HOLApp]
  }
  object HOLAppFormula {
    def apply(function: LambdaExpression, argument: LambdaExpression) = function.factory.createApp(function, argument).asInstanceOf[HOLAppFormula]
  }
  object HOLAbs {
    def apply(variable: Var, expression: LambdaExpression) = expression.factory.createAbs(variable, expression).asInstanceOf[HOLAbs]
  }

  case object NegC extends HOLConst(NegSymbol, "(o -> o)")
  case object AndC extends HOLConst(AndSymbol, "(o -> (o -> o))")
  case object OrC extends HOLConst(OrSymbol, "(o -> (o -> o))")
  case object ImpC extends HOLConst(ImpSymbol, "(o -> (o -> o))")

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
    def isFormula(typ: TA) = typ match {
      case To() => true
      case _ => false
    }
    def isFormulaWhenApplied(typ: TA) = typ match {
      case ->(in,To()) => true
      case _        => false
    }
  }

  object Definitions { def hol = HOLFactory }

  object ImplicitConverters {
    implicit def lambdaToHOL(exp: LambdaExpression): HOLTerm = exp.asInstanceOf[HOLTerm]
    implicit def listLambdaToListHOL(l: List[LambdaExpression]): List[HOLTerm] = l.asInstanceOf[List[HOLTerm]]
  }

  // We do in all of them additional casting into Formula as Formula is a static type and the only way to deynamically express it is via casting.
  object Neg {
    def apply(sub: Formula) = App(NegC,sub).asInstanceOf[HOLFormula]
    def unapply(expression: LambdaExpression) = expression match {
      case App(negC,sub) => Some( (sub.asInstanceOf[HOLFormula]) )
      case _ => None
    }
  }

  object And {
    def apply(left: Formula, right: Formula) = (App(App(AndC,left),right)).asInstanceOf[HOLFormula]
    def unapply(expression: LambdaExpression) = expression match {
      case App(App(andC,left),right) => Some( (left.asInstanceOf[HOLFormula],right.asInstanceOf[HOLFormula]) )
      case _ => None
    }
  }

  object Or {
    def apply(left: Formula, right: Formula) = App(App(OrC,left),right).asInstanceOf[HOLFormula]
    def unapply(expression: LambdaExpression) = expression match {
      case App(App(orC,left),right) => Some( (left.asInstanceOf[Formula],right.asInstanceOf[HOLFormula]) )
      case _ => None
    }
  }

  object Imp {
    def apply(left: Formula, right: Formula) = App(App(ImpC,left),right).asInstanceOf[HOLFormula]
    def unapply(expression: LambdaExpression) = expression match {
        case App(App(impC,left),right) => Some( (left.asInstanceOf[Formula],right.asInstanceOf[HOLFormula]) )
        case _ => None
    }
  }

  object BinaryFormula {
    def unapply(expression: LambdaExpression) = expression match {
        case And(left,right) => Some( (left,right) )
        case Or(left,right) => Some( (left,right) )
        case Imp(left,right) => Some( (left,right) )
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
      case App(sym,_) if sym.isInstanceOf[LogicalSymbolsA] => None
      case App(App(sym,_),_) if sym.isInstanceOf[LogicalSymbolsA] => None
      case AppN( Var( name, t ), args )
        if t == FunctionType( To(), args.map( a => a.exptype ) ) => Some( ( name, args ) )
      case _ => None
    }
  }
}
