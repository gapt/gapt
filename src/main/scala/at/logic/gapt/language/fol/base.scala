/*
 *
 * FOL's mini lambda-calculus and factory
 *
 */

package at.logic.gapt.language.fol

import at.logic.gapt.expr.{ LambdaExpression, Var, Const, App, Abs, FactoryA }
import at.logic.gapt.expr.symbols._
import at.logic.gapt.expr.types._
import at.logic.gapt.language.hol._
import at.logic.gapt.language.hol.logicSymbols._

class FOLVar( sym: SymbolA ) extends HOLVar( sym, Ti ) with FOLTerm
object FOLVar {
  def apply( name: String ): FOLVar = FOLFactory.createVar( StringSymbol( name ), Ti )
  def apply( sym: SymbolA ): FOLVar = FOLFactory.createVar( sym, Ti )
  def unapply( exp: FOLExpression ) = exp match {
    case v: FOLVar => Some( v.name )
    case _         => None
  }
}

// No factory for this because it shouldn't be used outside FOL
// In FOL, it is used to create the logical and predicate symbols
protected[fol] class FOLLambdaConst( sym: SymbolA, exptype: TA ) extends HOLConst( sym, exptype ) with FOLExpression
protected[fol] object FOLLambdaConst {
  def apply( name: String, exptype: TA ): FOLLambdaConst = FOLLambdaConst( StringSymbol( name ), exptype )
  def apply( sym: SymbolA, exptype: TA ): FOLLambdaConst = exptype match {
    case Ti => FOLConst( sym )
    case To => new FOLLambdaConst( sym, exptype ) with FOLFormula
    case _  => new FOLLambdaConst( sym, exptype )
  }
  def unapply( exp: FOLExpression ) = exp match {
    case c: FOLLambdaConst => Some( ( c.name, c.exptype ) )
    case _                 => None
  }
}

class FOLConst( sym: SymbolA ) extends FOLLambdaConst( sym, Ti ) with FOLTerm
object FOLConst {
  def apply( name: String ): FOLConst = FOLFactory.createConst( StringSymbol( name ), Ti ).asInstanceOf[FOLConst]
  def apply( sym: SymbolA ): FOLConst = FOLFactory.createConst( sym, Ti ).asInstanceOf[FOLConst]
  def unapply( exp: FOLExpression ) = exp match {
    case c: FOLConst => Some( c.name )
    case _           => None
  }
}

protected[fol] class FOLApp protected[fol] ( function: FOLExpression, arg: FOLExpression ) extends HOLApp( function, arg ) with FOLExpression
protected[fol] object FOLApp {
  def apply( f: FOLExpression, arg: FOLExpression ): FOLApp = f.factory.createApp( f, arg ).asInstanceOf[FOLApp]
  def unapply( e: FOLExpression ) = e match {
    case a: FOLApp => Some( ( a.function.asInstanceOf[FOLExpression], a.arg.asInstanceOf[FOLExpression] ) )
    case _         => None
  }
}

protected[fol] class FOLAbs protected[fol] ( variable: FOLVar, term: FOLExpression ) extends HOLAbs( variable, term ) with FOLExpression
protected[fol] object FOLAbs {
  def apply( variable: FOLVar, expression: FOLExpression ): FOLAbs = expression.factory.createAbs( variable, expression ).asInstanceOf[FOLAbs]
  def unapply( e: FOLExpression ) = e match {
    case a: FOLAbs => Some( ( a.variable.asInstanceOf[FOLVar], a.term.asInstanceOf[FOLExpression] ) )
    case _         => None
  }
}

/*********************** Factory *****************************/

object FOLFactory extends FactoryA {

  // We sometimes need to combine a logical constant from the HOL Layer
  // with some syntax from the FOL layer. We manually switch the constants
  // for the correct ones here.
  def switchLogicalConstants( c: LambdaExpression ): FOLExpression = c match {
    case HOLBottomC    => FOLBottomC
    case HOLTopC       => FOLTopC
    case HOLNegC       => FOLNegC
    case HOLAndC       => FOLAndC
    case HOLOrC        => FOLOrC
    case HOLImpC       => FOLImpC
    case HOLEqC( Ti )  => FOLEqC
    case HOLAllQ( Ti ) => FOLAllQ()
    case HOLExQ( Ti )  => FOLExQ()
    case _             => c.asInstanceOf[FOLExpression]
  }

  def createVar( sym: SymbolA, exptype: TA ): FOLVar = exptype match {
    case Ti => new FOLVar( sym )
    case _  => throw new Exception( "Trying to create a variable in FOL that has type different from i: " + exptype )
  }

  def createConst( sym: SymbolA, exptype: TA ): FOLConst = exptype match {
    case Ti => new FOLConst( sym )
    case _  => throw new Exception( "Trying to create a constant in FOL that has type different from i: " + exptype )
  }

  def createApp( fun: LambdaExpression, arg: LambdaExpression ): FOLApp = {
    val fun_ = switchLogicalConstants( fun )
    val arg_ = switchLogicalConstants( arg )
    // construct App
    fun_.exptype match {
      case ->( _, To ) => new FOLApp( fun_, arg_ ) with FOLFormula
      case ->( _, Ti ) => new FOLApp( fun_, arg_ ) with FOLTerm
      case _           => new FOLApp( fun_, arg_ )
    }
  }

  def createAbs( variable: Var, exp: LambdaExpression ): FOLAbs = {
    val exp_ = switchLogicalConstants( exp )
    new FOLAbs( variable.asInstanceOf[FOLVar], exp_ )
  }

  def createConnective( sym: SymbolA, tp: TA = Ti ): FOLLambdaConst = sym match {
    case BottomSymbol => FOLBottomC
    case TopSymbol    => FOLTopC
    case NegSymbol    => FOLNegC
    case AndSymbol    => FOLAndC
    case OrSymbol     => FOLOrC
    case ImpSymbol    => FOLImpC
    case EqSymbol     => FOLEqC
    case ForallSymbol => FOLAllQ()
    case ExistsSymbol => FOLExQ()
    case _            => throw new Exception( "Operator for " + sym.toString + " not defined for FOL." )
  }
}

