/*
 * fol.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */
package at.logic.language.fol

import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.hol
import at.logic.language.hol.propositions.{Neg => HOLNeg, Or => HOLOr, And => HOLAnd, Imp => HOLImp}
import at.logic.language.hol.propositions.{HOL, Formula, HOLVar, HOLConst, HOLApp, HOLAbs, HOLConstFormula, HOLFactory, HOLAppFormula}
import at.logic.language.hol.quantifiers.{All, Ex, AllQ, ExQ}
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.hol.logicSymbols._

trait FOL extends HOL
{
  override def factory : LambdaFactoryA = FOLFactory
}

trait FOLFormula extends LambdaExpression with HOL with Formula with FOL
//trait FOLFormula extends HOLFormula with FOL
trait FOLTerm extends LambdaExpression with HOL with FOL
// trait FOLTerm extends HOLTerm with FOL
{
  require( exptype == Ti() )
}

// individual variable
class FOLVar (name: VariableSymbolA)
  extends HOLVar(name, Ti()) with FOLTerm

// individual constant
class FOLConst (name: ConstantSymbolA)
  extends HOLConst(name, Ti()) with FOLTerm

class FOLApp(function: LambdaExpression, argument: LambdaExpression)
  extends HOLApp(function, argument) with FOL

class FOLAbs(variable: FOLVar, expression: LambdaExpression)
  extends HOLAbs(variable, expression) with FOL

object FOLAbs {
  def apply(variable: FOLVar, expression: LambdaExpression) = new FOLAbs(variable, expression)
}

object FOLVar {
  def apply(name: VariableSymbolA) = new FOLVar(name)
  def unapply(exp: LambdaExpression) = exp match {
    case Var( sym : VariableSymbolA, t : Ti ) => Some( sym )
    case _ => None
  }
}

object FOLConst {
  def apply(name: ConstantSymbolA) = new FOLConst(name)
  def unapply(exp: LambdaExpression) = exp match {
    case Var( sym : ConstantSymbolA, t : Ti ) => Some( sym )
    case _ => None
  }
}

object Func {
    def apply( sym: ConstantSymbolA, args: List[FOLTerm]) = {
      val pred : Var = FOLFactory.createVar( sym, FunctionType( Ti(), args.map( a => a.exptype ) ) )
      AppN(pred, args).asInstanceOf[FOLTerm]
    }
    def unapply( expression: LambdaExpression ) = expression match {
      case App(sym,_) if sym.isInstanceOf[LogicalSymbolsA] => None
      case App(App(sym,_),_) if sym.isInstanceOf[LogicalSymbolsA] => None
      case AppN( Var( name, t ), args )
        if t == FunctionType( Ti(), args.map( a => a.exptype ) ) => Some( ( name, args.asInstanceOf[List[FOLTerm]]) )
      case _ => None
    }
  }

// FOL atom of the form P(t_1,...,t_n)
object Atom {
  def apply( sym: ConstantSymbolA, args: List[FOLTerm]) = {
    val pred : Var = FOLFactory.createVar( sym, FunctionType( To(), args.map( a => Ti() ) ) )
    AppN(pred, args).asInstanceOf[FOLFormula]
  }
  def unapply( expression: LambdaExpression ) = expression match {
    case App(sym,_) if sym.isInstanceOf[LogicalSymbolsA] => None
    case App(App(sym,_),_) if sym.isInstanceOf[LogicalSymbolsA] => None
    case AppN( Var( name: ConstantSymbolA, t ), args )
      if t == FunctionType( To(), args.map( a => Ti() ) ) => Some( ( name, args.asInstanceOf[List[FOLTerm]] ) )
    case _ => None
  }
}

// FOL function of the form f(t_1,...,t_n)
object Function {
  def apply( sym: ConstantSymbolA, args: List[FOLTerm]) = {
    val f: Var = FOLFactory.createVar( sym, FunctionType( Ti(), args.map( a => Ti() ) ) )
    AppN( f, args ).asInstanceOf[FOLTerm]
  }
  def unapply( expression: LambdaExpression ) = expression match {
    case AppN( Var( name: ConstantSymbolA, t), args )
      if t == FunctionType( Ti(), args.map( a => Ti() ) ) => Some( (name, args.asInstanceOf[List[FOLTerm]] ) )
    case _ => None
  }
}

object Neg {
  def apply(sub: FOLFormula) = HOLNeg(sub).asInstanceOf[FOLFormula]
  def unapply(expression: LambdaExpression) = expression match {
    case HOLNeg(sub : FOLFormula) => Some( (sub) )
    case _ => None
  }
}

object And {
  def apply(left: FOLFormula, right: FOLFormula) = HOLAnd(left, right).asInstanceOf[FOLFormula]
  def unapply(expression: LambdaExpression) = expression match {
    case HOLAnd(left: FOLFormula, right: FOLFormula) => Some( left, right )
    case _ => None
  }
}

object Or {
  def apply(left: FOLFormula, right: FOLFormula) = HOLOr(left, right).asInstanceOf[FOLFormula]
  def unapply(expression: LambdaExpression) = expression match {
    case HOLOr(left: FOLFormula, right: FOLFormula) => Some( left, right )
    case _ => None
  }
}

object Imp {
  def apply(left: FOLFormula, right: FOLFormula) = HOLImp(left, right).asInstanceOf[FOLFormula]
  def unapply(expression: LambdaExpression) = expression match {
      case HOLImp(left: FOLFormula, right: FOLFormula) => Some( left, right )
      case _ => None
  }
}

object ExVar {
  def apply(variable: FOLVar, sub: FOLFormula) = Ex(FOLAbs(variable, sub))
  def unapply(expression: LambdaExpression) = expression match {
    case Ex(Abs(variable: FOLVar, sub: FOLFormula)) => Some( (variable, sub) )
    case _ => None
  }
}

object AllVar {
  def apply(variable: FOLVar, sub: FOLFormula) = All(FOLAbs(variable, sub))
  def unapply(expression: LambdaExpression) = expression match {
    case All(Abs(variable: FOLVar, sub: FOLFormula)) => Some( (variable, sub) )
    case _ => None
  }
}

object FOLFactory extends LambdaFactoryA {
  def createVar( name: SymbolA, exptype: TA ) : Var = exptype match {
    case Ti() => name match {
      case a: ConstantSymbolA => FOLConst(a)
      case a: VariableSymbolA => FOLVar(a)
    }
    case To() => name match {
      case a: ConstantSymbolA => new HOLConstFormula(a) with FOL
      case _ => throw new Exception("In FOL, of type 'o' only constants may be created.")
    }
    case ->(tr, ta) => {
      if (!(isFirstOrderType(exptype)))
        throw new Exception("In FOL, cannot create a symbol of type " + exptype)
      name match {
        case a: ConstantSymbolA => new HOLConst(a, exptype) with FOL
        case _ => throw new Exception("In FOL, of type 'a -> b' only constants may be created.")
      }
    }
  }

  def createApp( fun: LambdaExpression, arg: LambdaExpression ) : App =
    if (HOLFactory.isFormulaWhenApplied(fun.exptype)) new HOLAppFormula(fun, arg) with FOLFormula
    else if (isTermWhenApplied(fun.exptype)) new FOLApp(fun, arg) with FOLTerm
    else new FOLApp(fun, arg)

  def createAbs( variable: Var, exp: LambdaExpression ) : Abs =  new HOLAbs( variable, exp ) with FOL

  private def isTermWhenApplied(typ: TA) = typ match {
    case ->(_,Ti()) => true
    case _ => false
  }

  private def isFirstOrderType( exptype: TA ) = isFunctionType( exptype ) || isPredicateType( exptype )

  private def isFunctionType( exptype: TA ) = checkType( exptype, Ti(), Ti() ) 

  private def isPredicateType( exptype: TA ) = checkType( exptype, To(), Ti() )

  private def checkType( toCheck: TA, retType : TA, argType: TA ) : Boolean =
    toCheck match {
      case t : Ti => t == retType
      case t : To => t == retType
      case ->(ta, tr) => ta == argType && checkType( tr, retType, argType )
    }
}
