/*
 *
 * Schema's mini lambda-calculus and factory
 *
 */

package at.logic.language.schema

import at.logic.language.lambda.{LambdaExpression, Var, Const, App, Abs, FactoryA}
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.hol.{HOLVar, HOLConst, HOLApp, HOLAbs}
import at.logic.language.hol.logicSymbols._

class SchemaVar protected[schema] (sym: SymbolA, exptype: TA) extends HOLVar(sym, exptype) with SchemaExpression 
object SchemaVar {
  def apply(name: String, exptype: TA) : SchemaVar = SchemaFactory.createVar(StringSymbol(name), exptype)
  def unapply(exp: SchemaExpression) = exp match {
    case v: SchemaVar => Some( (v.name, v.exptype) )
    case _ => None
  }
}

class SchemaConst protected[schema] (sym: SymbolA, exptype: TA) extends HOLConst(sym, exptype) with SchemaExpression
object SchemaConst {
  def apply(name: String, exptype: TA) : SchemaConst = SchemaFactory.createConst(StringSymbol(name), exptype)
  def apply(sym: SymbolA, exptype: TA) : SchemaConst = SchemaFactory.createConst(sym, exptype)
  def apply(name: String, exptype: String) : SchemaConst = SchemaFactory.createConst(StringSymbol(name), Type(exptype))
  def unapply(exp: SchemaExpression) = exp match {
    case c: SchemaConst => Some( (c.name, c.exptype) )
    case _ => None
  }
}

class SchemaApp private[schema] (function: SchemaExpression, arg: SchemaExpression) extends HOLApp(function, arg) with SchemaExpression
object SchemaApp {
  def apply(function: SchemaExpression, argument: SchemaExpression) : SchemaApp = argument.factory.createApp(function, argument).asInstanceOf[SchemaApp]
  def apply(function: SchemaExpression, arguments: List[SchemaExpression]) : SchemaExpression = arguments match {
    case Nil => function
    case h :: tl => apply(SchemaApp(function, h), tl)
  }
  def unapply(e: SchemaExpression) = e match {
    case a: SchemaApp => Some( (a.function.asInstanceOf[SchemaExpression], a.arg.asInstanceOf[SchemaExpression]) )
    case _ => None
  }
}

class SchemaAbs private[schema] (variable: SchemaVar, expression: SchemaExpression) extends HOLAbs(variable, expression) with SchemaExpression
object SchemaAbs {
  def apply(v: SchemaVar, e: SchemaExpression) : SchemaAbs = e.factory.createAbs(v, e).asInstanceOf[SchemaAbs]
  def unapply(e: SchemaExpression) = e match {
    case a: SchemaAbs => Some( (a.variable.asInstanceOf[IntVar], a.term.asInstanceOf[SchemaExpression]) )
    case _ => None
  }
}

/*********************** Factory *****************************/

object SchemaFactory extends FactoryA {
  def createVar( name: SymbolA, exptype: TA) : SchemaVar = exptype match {
    case To => new SchemaVar(name, exptype) with SchemaFormula
    case Tindex => new IntVar(name)
    case _ => new SchemaVar(name, exptype)
  }
  
  def createConst(name: SymbolA, exptype: TA) : SchemaConst = exptype match {
    case To => new SchemaConst(name, exptype) with SchemaFormula
    case Tindex => new IntConst(name)
    case _ => new SchemaConst(name, exptype)
  }
  
  def createApp( fun: LambdaExpression, arg: LambdaExpression ): SchemaApp = fun.exptype match {
    case ->(_, To) => new SchemaApp(fun.asInstanceOf[SchemaExpression], arg.asInstanceOf[SchemaExpression]) with SchemaFormula
    case ->(_, Tindex) => new SchemaApp(fun.asInstanceOf[SchemaExpression], arg.asInstanceOf[SchemaExpression]) with IntegerTerm
    case _ => new SchemaApp(fun.asInstanceOf[SchemaExpression], arg.asInstanceOf[SchemaExpression])
  }
  
  def createAbs( variable: Var, exp: LambdaExpression ): SchemaAbs = new SchemaAbs( variable.asInstanceOf[SchemaVar], exp.asInstanceOf[SchemaExpression] )
  
  def createConnective(sym: SymbolA, tp: TA = Ti) : SchemaConst = sym match {
    case BottomSymbol => BottomC
    case TopSymbol => TopC
    case NegSymbol => NegC
    case AndSymbol => AndC
    case OrSymbol => OrC
    case ImpSymbol => ImpC
    case EqSymbol => EqC(tp)
    case ForallSymbol => AllQ(tp)
    case ExistsSymbol => ExQ(tp)
    case _ => throw new Exception("Operator for " + sym.toString + " not defined for HOL.")
  }
}
