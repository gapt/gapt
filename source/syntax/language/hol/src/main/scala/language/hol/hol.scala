/*
 * hol.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language

import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.lambda.typedLambdaCalculus._

package hol {

  trait Formula extends LambdaExpression {require(exptype == To())}
  trait Const
  trait HOL extends LambdaFactoryProvider {
    override def factory : LambdaFactoryA = HOLFactory
  }

  trait HOLExpression extends LambdaExpression with HOL {
    override def toString = this match {
      case Var(x,tpe) => x.toString + ":" + tpe.toString
      case Atom(x, args) => x + "(" +
        (if (args.size > 1) args.head.toString + args.tail.foldLeft("")((s,a) => s+", "+a.toString)
        else args.foldLeft("")((s,a) => s+a.toString)) + "): o"
      case Function(x, args, tpe) => x + "(" +
        (if (args.size > 1) args.head.toString + args.tail.foldLeft("")((s,a) => s+", "+a.toString)
        else args.foldLeft("")((s,a) => s+a.toString)) + "):" + tpe.toString
      case And(x,y) => "(" + x.toString + AndSymbol + y.toString + ")"
      case Or(x,y) => "(" + x.toString + OrSymbol + y.toString + ")"
      case Imp(x,y) => "(" + x.toString + ImpSymbol + y.toString + ")"
      case Neg(x) => NegSymbol + x.toString
      case ExVar(x,f) => ExistsSymbol + x.toString + "." + f.toString
      case AllVar(x,f) => ForallSymbol + x.toString + "." + f.toString
      case AbsInScope(v, exp) => "(λ" + v.toString + "." + exp.toString + ")"
      case App(l, r) => "(" + l.toString + ")" + "(" + r.toString + ")"
    }
  }
  trait HOLFormula extends HOLExpression with Formula {
    def and(that: HOLFormula) =  And(this, that)
    def or(that: HOLFormula) = Or(this, that)
    def imp(that: HOLFormula) = Imp(this, that)
  }

  class HOLVar protected[hol] (name: VariableSymbolA, exptype: TA, dbInd: Option[Int])
    extends Var(name, exptype, dbInd) with HOLExpression
  class HOLConst protected[hol] (name: ConstantSymbolA, exptype: TA)
    extends Var(name, exptype, None) with Const with HOLExpression
  class HOLVarFormula protected[hol] (name: VariableSymbolA, dbInd: Option[Int])
    extends HOLVar(name, To(), dbInd) with HOLFormula
  class HOLConstFormula protected[hol] (name: ConstantSymbolA)
    extends HOLConst(name, To()) with HOLFormula
  class HOLApp protected[hol] (function: LambdaExpression, argument: LambdaExpression)
    extends App(function, argument) with HOLExpression
  class HOLAppFormula protected[hol] (function: LambdaExpression, argument: LambdaExpression)
    extends HOLApp(function, argument) with HOLFormula
  class HOLAbs protected[hol] (variable: Var, expression: LambdaExpression)
    extends Abs(variable, expression) with HOLExpression

  object HOLVar {
    def apply(name: VariableSymbolA, exptype: TA) = HOLFactory.createVar(name, exptype).asInstanceOf[HOLVar]
    def unapply(exp: LambdaExpression) = exp match {
      case Var(n: VariableSymbolA, t) => Some( n, t )
      case _ => None
    }
  }
  object HOLConst {
    def apply(name: ConstantSymbolA, exptype: TA) = HOLFactory.createVar(name, exptype).asInstanceOf[HOLConst]
    def unapply(exp: LambdaExpression) = exp match {
      case Var(n: ConstantSymbolA, t) => Some( n, t )
      case _ => None
    }
  }
  object HOLVarFormula {
    def apply(name: VariableSymbolA) = HOLFactory.createVar(name, To()).asInstanceOf[HOLVarFormula]
  }
  object HOLConstFormula {
    def apply(name: ConstantSymbolA) = HOLFactory.createVar(name, To()).asInstanceOf[HOLConstFormula]
  }
  object HOLApp {
    def apply(function: LambdaExpression, argument: LambdaExpression) = function.factory.createApp(function, argument).asInstanceOf[HOLApp]
    def unapply(exp: LambdaExpression) = exp match {
      case App(t1: HOLExpression, t2: HOLExpression) => Some( ( t1, t2 ) )
      case _ => None
    }
  }
  object HOLAppFormula {
    def apply(function: LambdaExpression, argument: LambdaExpression) = function.factory.createApp(function, argument).asInstanceOf[HOLAppFormula]
  }
  object HOLAbs {
    def apply(variable: Var, expression: LambdaExpression) = expression.factory.createAbs(variable, expression).asInstanceOf[HOLAbs]
    def unapply(exp: LambdaExpression) = exp match {
      case Abs(v: HOLVar, sub: HOLExpression) => Some( (v, sub) )
      case _ => None
    }
  }

  /*
   * This extractor contains the binding information in the variable and in the expression
   */
  object HOLAbsInScope {
    def unapply(expression: LambdaExpression) = expression match {
      case a : Abs if a.variable.isInstanceOf[HOLVar] && a.expression.isInstanceOf[HOLExpression] =>
        Some((a.variableInScope.asInstanceOf[HOLVar], a.expressionInScope.asInstanceOf[HOLExpression]))
      case _ => None
    }
  }

  case object BottomC extends HOLConst(BottomSymbol, "o") with HOLFormula
  case object TopC extends HOLConst(TopSymbol, "o") with HOLFormula
  case object NegC extends HOLConst(NegSymbol, "(o -> o)")
  case object AndC extends HOLConst(AndSymbol, "(o -> (o -> o))")
  case object OrC extends HOLConst(OrSymbol, "(o -> (o -> o))")
  case object ImpC extends HOLConst(ImpSymbol, "(o -> (o -> o))")
  class ExQ protected[hol](e:TA) extends HOLConst(ExistsSymbol, ->(e,"o"))
  class AllQ protected[hol](e:TA) extends HOLConst(ForallSymbol, ->(e,"o"))

  object HOLFactory extends LambdaFactoryA {
    def createVar( name: SymbolA, exptype: TA, dbInd: Option[Int]) : Var =
      name match {
        case a: ConstantSymbolA =>
          if (isFormula(exptype)) new HOLConstFormula(a)
          else new HOLConst(a, exptype)
        case a: VariableSymbolA =>
          if (isFormula(exptype)) new HOLVarFormula(a,dbInd)
          else new HOLVar(a, exptype,dbInd)
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
    implicit def lambdaToHOL(exp: LambdaExpression): HOLExpression = exp.asInstanceOf[HOLExpression]
    implicit def listLambdaToListHOL(l: List[LambdaExpression]): List[HOLExpression] = l.asInstanceOf[List[HOLExpression]]
  }

  // We do in all of them additional casting into Formula as Formula is a static type and the only way to dynamically express it is via casting.
  object Neg {
    def apply(sub: HOLFormula) = App(NegC,sub).asInstanceOf[HOLFormula]
    def unapply(expression: LambdaExpression) = expression match {
      case App(NegC,sub) => Some( (sub.asInstanceOf[HOLFormula]) )
      case _ => None
    }
  }

  object And {
    def apply(left: HOLFormula, right: HOLFormula) = (App(App(AndC,left),right)).asInstanceOf[HOLFormula]
    def unapply(expression: LambdaExpression) = expression match {
      case App(App(AndC,left),right) => Some( (left.asInstanceOf[HOLFormula],right.asInstanceOf[HOLFormula]) )
      case _ => None
    }
  }

  object Or {
    def apply(fs: List[HOLFormula]) : HOLFormula = fs match {
      case Nil => BottomC
      case f::fs => fs.foldLeft(f)( (d, f) => Or(d, f) )
    }
    def apply(left: HOLFormula, right: HOLFormula) : HOLFormula = App(App(OrC,left),right).asInstanceOf[HOLFormula]
    def unapply(expression: LambdaExpression) = expression match {
      case App(App(OrC,left),right) => Some( (left.asInstanceOf[HOLFormula],right.asInstanceOf[HOLFormula]) )
      case _ => None
    }
  }

  object Imp {
    def apply(left: HOLFormula, right: HOLFormula) = App(App(ImpC,left),right).asInstanceOf[HOLFormula]
    def unapply(expression: LambdaExpression) = expression match {
        case App(App(ImpC,left),right) => Some( (left.asInstanceOf[HOLFormula],right.asInstanceOf[HOLFormula]) )
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

  object Function {
    def apply( sym: SymbolA, args: List[HOLExpression], returnType: TA): HOLExpression = {
      val pred : Var = HOLFactory.createVar( sym, FunctionType( returnType, args.map( a => a.exptype ) ) )
      apply(pred, args)
    }
    def apply(head: Var, args: List[HOLExpression]): HOLExpression = {
      AppN(head, args).asInstanceOf[HOLExpression]
    }
    def unapply( expression: LambdaExpression ) = expression match {
      case App(sym,_) if sym.isInstanceOf[LogicalSymbolsA] => None
      case App(App(sym,_),_) if sym.isInstanceOf[LogicalSymbolsA] => None
      case AppN( Var( name, t ), args ) if (expression.exptype != To()) => Some( ( name, args, expression.exptype ) )
      case _ => None
    }
  }
  // HOL formulas of the form P(t_1,...,t_n)
  object Atom {
    def apply( sym: SymbolA, args: List[HOLExpression]): HOLFormula = {
      val pred : Var = HOLFactory.createVar( sym, FunctionType( To(), args.map( a => a.exptype ) ) )
      apply(pred, args)
    }
    def apply(head: Var, args: List[HOLExpression]): HOLFormula = {
      AppN(head, args).asInstanceOf[HOLFormula]
    }
    def unapply( expression: LambdaExpression ) = expression match {
      case App(sym,_) if sym.isInstanceOf[LogicalSymbolsA] => None
      case App(App(sym,_),_) if sym.isInstanceOf[LogicalSymbolsA] => None
      case AppN( Var( name, t ), args ) if (expression.exptype == To()) => Some( ( name, args ) )
      case _ => None
    }
  }

object ExQ {
    def unapply(v: Var) = v match {
      case vo: ExQ => Some(vo.exptype)
      case _ => None
    }
  }
  object AllQ {
    def unapply(v: Var) = v match {
      case vo: AllQ => Some(vo.exptype)
      case _ => None
    }
  }

  object Ex {
    def apply(sub: LambdaExpression) = App(new ExQ(sub.exptype),sub).asInstanceOf[HOLFormula]
    def unapply(expression: LambdaExpression) = expression match {
      case App(ExQ(t),sub) => Some( (sub, t) )
      case _ => None
    }
  }

  object All {
    def apply(sub: LambdaExpression) = App(new AllQ(sub.exptype),sub).asInstanceOf[HOLFormula]
    def unapply(expression: LambdaExpression) = expression match {
      case App(AllQ(t),sub) => Some( (sub, t) )
      case _ => None
    }
  }

  object ExVar {
    def apply(variable: Var, sub: HOLFormula) = Ex(Abs(variable, sub))
    def unapply(expression: LambdaExpression) = expression match {
      case Ex(Abs(variable, sub), _) => Some( (variable, sub.asInstanceOf[HOLFormula]) )
      case _ => None
    }
  }

  object AllVar {
    def apply(variable: Var, sub: HOLFormula) = All(Abs(variable, sub))
    def unapply(expression: LambdaExpression) = expression match {
      case All(Abs(variable, sub), _) => Some( (variable, sub.asInstanceOf[HOLFormula]) )
      case _ => None
    }
  }

  object Quantifier {
    def unapply(expression: LambdaExpression) = expression match {
      case ExVar(x, f) => Some(ExistsSymbol, x, f)
      case AllVar(x, f) => Some(ForallSymbol, x, f)
      case _ => None
    }
  }
}

