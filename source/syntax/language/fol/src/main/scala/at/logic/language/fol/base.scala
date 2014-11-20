/*
 *
 * FOL's mini lambda-calculus and factory
 *
 */

package at.logic.language.fol

import at.logic.language.lambda.{LambdaExpression, Var, Const, App, Abs, FactoryA}
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.hol.{HOLVar, HOLConst, HOLApp, HOLAbs}
import at.logic.language.hol.logicSymbols._

class FOLVar (sym: SymbolA) extends HOLVar(sym, Ti) with FOLTerm
object FOLVar {
  def apply(name: String) : FOLVar = FOLFactory.createVar(StringSymbol(name), Ti)
  def apply(sym: SymbolA) : FOLVar = FOLFactory.createVar(sym, Ti)
  def unapply(exp: FOLExpression) = exp match {
    case v: FOLVar => Some( v.name )
    case _ => None
  }
}

// No factory for this because it shouldn't be used outside FOL
// In FOL, it is used to create the logical and predicate symbols
protected[fol] class FOLLambdaConst (sym: SymbolA, exptype: TA) extends HOLConst(sym, exptype) with FOLExpression
protected[fol] object FOLLambdaConst {
  def apply(name: String, exptype: TA) : FOLLambdaConst = FOLLambdaConst(StringSymbol(name), exptype)
  def apply(sym: SymbolA, exptype: TA) : FOLLambdaConst = exptype match {
    case Ti => FOLConst(sym)
    case To => new FOLLambdaConst(sym, exptype) with FOLFormula
    case _ => new FOLLambdaConst(sym, exptype)
  }
  def unapply(exp: FOLExpression) = exp match {
    case c: FOLLambdaConst => Some( (c.name, c.exptype) )
    case _ => None
  }
}

class FOLConst (sym: SymbolA) extends FOLLambdaConst(sym, Ti) with FOLTerm
object FOLConst {
  def apply(name: String) : FOLConst = FOLFactory.createConst(StringSymbol(name), Ti).asInstanceOf[FOLConst]
  def apply(sym: SymbolA) : FOLConst = FOLFactory.createConst(sym, Ti).asInstanceOf[FOLConst]
  def unapply(exp: FOLExpression) = exp match {
    case c: FOLConst => Some( c.name )
    case _ => None
  }
}

protected[fol] class FOLApp protected[fol] (function: FOLExpression, arg: FOLExpression) extends HOLApp(function, arg) with FOLExpression
protected[fol] object FOLApp {
  def apply(f: FOLExpression, arg: FOLExpression) : FOLApp = f.factory.createApp(f, arg).asInstanceOf[FOLApp] 
  def unapply(e: FOLExpression) = e match {
    case a: FOLApp => Some( (a.function.asInstanceOf[FOLExpression], a.arg.asInstanceOf[FOLExpression]) )
    case _ => None
  }
}

protected[fol] class FOLAbs protected[fol] (variable: FOLVar, term: FOLExpression) extends HOLAbs(variable, term) with FOLExpression
protected[fol] object FOLAbs {
  def apply(variable: FOLVar, expression: FOLExpression) : FOLAbs = expression.factory.createAbs(variable, expression).asInstanceOf[FOLAbs]
  def unapply(e: FOLExpression) = e match {
    case a: FOLAbs => Some( (a.variable.asInstanceOf[FOLVar], a.term.asInstanceOf[FOLExpression]) )
    case _ => None
  }
}

/*********************** Factory *****************************/

object FOLFactory extends FactoryA {

  // We sometimes need to combine a logical constant from the HOL Layer
  // with some syntax from the FOL layer. We manually switch the constants
  // for the correct ones here.
  def switchLogicalConstants( c: LambdaExpression ) : FOLExpression = c match {
    case at.logic.language.hol.BottomC => BottomC
    case at.logic.language.hol.TopC => TopC
    case at.logic.language.hol.NegC => NegC
    case at.logic.language.hol.AndC => AndC
    case at.logic.language.hol.OrC => OrC
    case at.logic.language.hol.ImpC => ImpC
    case at.logic.language.hol.EqC(Ti) => EqC
    case at.logic.language.hol.AllQ(Ti) => AllQ()
    case at.logic.language.hol.ExQ(Ti) => ExQ()
    case _ => c.asInstanceOf[FOLExpression]
  }
  
  def createVar( sym: SymbolA, exptype: TA ) : FOLVar = exptype match {
    case Ti => new FOLVar(sym)
    case _ => throw new Exception("Trying to create a variable in FOL that has type different from i: " + exptype)
  }
  
  def createConst( sym: SymbolA, exptype: TA ) : FOLConst = exptype match {
    case Ti => new FOLConst(sym)
    case _ => throw new Exception("Trying to create a constant in FOL that has type different from i: " + exptype)
  }

  def createApp( fun: LambdaExpression, arg: LambdaExpression ) : FOLApp = {
    val fun_ = switchLogicalConstants(fun)
    val arg_ = switchLogicalConstants(arg)
    // construct App
    fun_.exptype match {
      case ->(_, To) => new FOLApp(fun_, arg_) with FOLFormula
      case ->(_, Ti) => new FOLApp(fun_, arg_) with FOLTerm
      case _ => new FOLApp(fun_, arg_)
    }
  }

  def createAbs( variable: Var, exp: LambdaExpression ) : FOLAbs = {
    val exp_ = switchLogicalConstants( exp )
    new FOLAbs( variable.asInstanceOf[FOLVar], exp_ )
  }

  def createConnective(sym: SymbolA, tp: TA = Ti) : FOLLambdaConst = sym match {
    case BottomSymbol => BottomC
    case TopSymbol => TopC
    case NegSymbol => NegC
    case AndSymbol => AndC
    case OrSymbol => OrC
    case ImpSymbol => ImpC
    case EqSymbol => EqC
    case ForallSymbol => AllQ()
    case ExistsSymbol => ExQ()
    case _ => throw new Exception("Operator for " + sym.toString + " not defined for FOL.")
  }
}


