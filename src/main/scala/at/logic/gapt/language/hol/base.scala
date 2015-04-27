/*
 *
 * HOL's mini lambda-calculus and factory
 *
 */

package at.logic.gapt.language.hol

import at.logic.gapt.language.hol.logicSymbols._
import at.logic.gapt.language.lambda.symbols._
import at.logic.gapt.language.lambda.types._
import at.logic.gapt.language.lambda.{ Abs, App, Const, FactoryA, LambdaExpression, Var }

class HOLVar protected[hol] ( sym: SymbolA, exptype: TA ) extends Var( sym, exptype ) with HOLExpression

object HOLVar {
  def apply( name: String, exptype: TA ): HOLVar = HOLFactory.createVar( StringSymbol( name ), exptype )
  def apply( sym: SymbolA, exptype: TA ): HOLVar = HOLFactory.createVar( sym, exptype )
  def unapply( exp: HOLExpression ) = exp match {
    case v: HOLVar => Some( ( v.name, v.exptype ) )
    case _         => None
  }
}

class HOLConst protected[hol] ( sym: SymbolA, exptype: TA ) extends Const( sym, exptype ) with HOLExpression

object HOLConst {
  def apply( name: String, exptype: TA ): HOLConst = HOLFactory.createConst( StringSymbol( name ), exptype )
  def apply( sym: SymbolA, exptype: TA ): HOLConst = HOLFactory.createConst( sym, exptype )
  def apply( name: String, exptype: String ): HOLConst = HOLFactory.createConst( StringSymbol( name ), Type( exptype ) )
  def unapply( exp: HOLExpression ) = exp match {
    case c: HOLConst => Some( ( c.name, c.exptype ) )
    case _           => None
  }
}

class HOLApp protected[hol] ( function: HOLExpression, arg: HOLExpression ) extends App( function, arg ) with HOLExpression

object HOLApp {
  def apply( function: HOLExpression, argument: HOLExpression ): HOLApp = function.factory.createApp( function, argument ).asInstanceOf[HOLApp]
  def apply( function: HOLExpression, arguments: List[HOLExpression] ): HOLExpression = arguments match {
    case Nil     => function
    case h :: tl => apply( HOLApp( function, h ), tl )
  }
  def unapply( exp: HOLExpression ) = exp match {
    case a: HOLApp => Some( ( a.function.asInstanceOf[HOLExpression], a.arg.asInstanceOf[HOLExpression] ) )
    case _         => None
  }
}

class HOLAbs( variable: HOLVar, term: HOLExpression ) extends Abs( variable, term ) with HOLExpression

object HOLAbs {
  def apply( variable: HOLVar, expression: HOLExpression ): HOLAbs = expression.factory.createAbs( variable, expression ).asInstanceOf[HOLAbs]
  def unapply( exp: HOLExpression ) = exp match {
    case a: HOLAbs => Some( ( a.variable.asInstanceOf[HOLVar], a.term.asInstanceOf[HOLExpression] ) )
    case _         => None
  }
}

/*********************** Factory *****************************/

object HOLFactory extends FactoryA {

  def createVar( sym: SymbolA, exptype: TA ): HOLVar = exptype match {
    case To => new HOLVar( sym, exptype ) with HOLFormula
    case _  => new HOLVar( sym, exptype )
  }

  def createConst( sym: SymbolA, exptype: TA ): HOLConst = exptype match {
    case To => new HOLConst( sym, exptype ) with HOLFormula
    case _  => new HOLConst( sym, exptype )
  }

  def createApp( fun: LambdaExpression, arg: LambdaExpression ): HOLApp = fun.exptype match {
    case ->( _, To ) => new HOLApp( fun.asInstanceOf[HOLExpression], arg.asInstanceOf[HOLExpression] ) with HOLFormula
    case _           => new HOLApp( fun.asInstanceOf[HOLExpression], arg.asInstanceOf[HOLExpression] )
  }

  def createAbs( variable: Var, exp: LambdaExpression ): HOLAbs = new HOLAbs( variable.asInstanceOf[HOLVar], exp.asInstanceOf[HOLExpression] )

  def createConnective( sym: SymbolA, tp: TA = Ti ): HOLConst = sym match {
    case BottomSymbol => HOLBottomC
    case TopSymbol    => HOLTopC
    case NegSymbol    => HOLNegC
    case AndSymbol    => HOLAndC
    case OrSymbol     => HOLOrC
    case ImpSymbol    => HOLImpC
    case EqSymbol     => HOLEqC( tp )
    case ForallSymbol => HOLAllQ( tp )
    case ExistsSymbol => HOLExQ( tp )
    case _            => throw new Exception( "Operator for " + sym.toString + " not defined for HOL." )
  }
}

