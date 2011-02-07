package at.logic.language.schemata

/*The definition of Indexed proposition is taken from:
 * A Schemata Calculus for Propositional Logic by Vincent Aravantinos, Ricardo Caferra, and Nicolas Peltier
 **/


import at.logic.language.lambda.types._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.fol._
import at.logic.language.lambda.symbols._
import at.logic.language.hol._
import at.logic.language.hol.logicSymbols._
import at.logic.language.schemata.logicSymbols._


trait Schema extends HOL {
//  override def factory: LambdaFactoryA = FOLSchemataFactory
}

trait SchemataExpression extends HOLExpression with Schema {}



trait IntegerTermExpression extends SchemataExpression with Schema {
//  def exptype = Tindex()
//  def isPredecessorOf(i: IntegerTermExpression): Boolean = i match {
//    case
//  }
}

class IntVar (name: VariableSymbolA) extends HOLVar(name, Tindex(), None) with IntegerTermExpression {}
case object IntVar {
  def apply(name: VariableSymbolA) = IntegerTermFactory.createVar(name)
}


class IntConst  extends HOLConst(ConstantStringSymbol("0"), Tindex()) with IntegerTermExpression {}
case object IntConst {
  def apply = IntegerTermFactory.createVar(ConstantStringSymbol("0"))
  def toInt: Int = 0
}

case object Succ extends HOLConst(new ConstantStringSymbol("s"), ->(Tindex(), Tindex()))
case object PlusC extends HOLConst(new ConstantStringSymbol("+"), ->(Tindex(), ->(Tindex(), Tindex())))
case object TimesC extends HOLConst(new ConstantStringSymbol("×"), ->(Tindex(), ->(Tindex(), Tindex())))


class Succ {
  def apply(t: IntegerTermExpression): IntegerTermExpression  = IntegerTermFactory.createSucc(t)
  def unapply(p: IntegerTermExpression) = p match {
    case App(Succ, t) => Some(t)
    case _ => None
  }
}

class Plus {}
object Plus {
  def apply(t1: IntegerTermExpression, t2:IntegerTermExpression): IntegerTermExpression  = IntegerTermFactory.createPlus(t1,t2)
}

class Times  {}
object Times {
  def apply(t1: IntegerTermExpression, t2:IntegerTermExpression): IntegerTermExpression  = IntegerTermFactory.createTimes(t1,t2)
}

object IntegerTermFactory /*extends LambdaFactoryA*/ {
//  def toInt(exp: IntegerTermExpression): Int = exp match {
  def createVar( name: SymbolA): Var = name match {
    case a: ConstantSymbolA => IntConst.asInstanceOf[Var]
    case a: VariableSymbolA => IntVar(a)
  }
  def createSucc(t: IntegerTermExpression): IntegerTermExpression =  App(Succ, t).asInstanceOf[IntegerTermExpression]
  def createPlus(t1: IntegerTermExpression, t2:IntegerTermExpression): IntegerTermExpression  = AppN(PlusC, t1::t2::Nil).asInstanceOf[IntegerTermExpression]
  def createTimes(t1: IntegerTermExpression, t2:IntegerTermExpression): IntegerTermExpression  = AppN(TimesC, t1::t2::Nil).asInstanceOf[IntegerTermExpression]
}
//------------------------------------------------------------------------------------------------


class IndexedPredicateVar(sym: VariableSymbolA, val index: List[IntegerTermExpression], exptype: TA) extends HOLVar(sym, exptype, None) with SchemataFormula {
  def arity:Int = index.size
}

object IndexedPredicateVar {
  def apply(s: VariableSymbolA, indexTerms: List[IntegerTermExpression], tp: TA): SchemataExpression = FOLSchemataFactory.createVar(s, indexTerms, tp)

  def apply(s: VariableSymbolA, indexTerm: IntegerTermExpression, tp: TA): SchemataExpression = {
    new IndexedPredicateVar(s, indexTerm::Nil, tp)
  }
}



//-------------------------------------------------------------------------------------------------

trait SchemataFormula extends SchemataExpression {
//  def and(that: SchemataFormula) =  And(this, that)
//  def or(that: SchemataFormula) = Or(this, that)
//  def imp(that: SchemataFormula) = Imp(this, that)
//  def bigAnd(begin: IntegerTermExpression, end: IntegerTermExpression, v: IndexedPredicateVar) =  BigAnd(begin, end, v)
//  def bigOr(begin: IntegerTermExpression, end: IntegerTermExpression, v: IndexedPredicateVar) =  BigOr(begin, end, v)
}

object Neg {
  def apply(sub: SchemataFormula) = App(NegC,sub).asInstanceOf[SchemataFormula]
  def unapply(expression: LambdaExpression) = expression match {
    case App(NegC,sub) => Some( (sub.asInstanceOf[SchemataFormula]) )
    case _ => None
  }
}

object And {
  def apply(left: SchemataFormula, right: SchemataFormula) = (App(App(AndC,left),right)).asInstanceOf[SchemataFormula]
  def unapply(expression: LambdaExpression) = expression match {
    case App(App(AndC,left),right) => Some( (left.asInstanceOf[SchemataFormula],right.asInstanceOf[SchemataFormula]) )
    case _ => None
  }
}

object Or {
  def apply(left: SchemataFormula, right: SchemataFormula) = App(App(OrC,left),right).asInstanceOf[SchemataFormula]
  def unapply(expression: LambdaExpression) = expression match {
    case App(App(OrC,left),right) => Some( (left.asInstanceOf[SchemataFormula],right.asInstanceOf[SchemataFormula]) )
    case _ => None
  }
}

object Imp {
  def apply(left: SchemataFormula, right: SchemataFormula) = App(App(ImpC,left),right).asInstanceOf[SchemataFormula]
  def unapply(expression: LambdaExpression) = expression match {
      case App(App(ImpC,left),right) => Some( (left.asInstanceOf[SchemataFormula],right.asInstanceOf[SchemataFormula]) )
      case _ => None
  }
}

object BigAnd {
  def apply(iter: IntVar, init: IntegerTermExpression, end: IntegerTermExpression, sf : SchemataFormula) = AppN(BigAndC, iter::init::end::sf::Nil).asInstanceOf[SchemataFormula]
}

object BigOr {
  def apply(iter: IntVar, init: IntegerTermExpression, end: IntegerTermExpression, sf : SchemataFormula) = AppN(BigOrC, iter::init::end::sf::Nil).asInstanceOf[SchemataFormula]
}

case object BottomC extends HOLConst(BottomSymbol, To()) with SchemataFormula
case object NegC extends HOLConst(NegSymbol, ->(To(), To())) with SchemataFormula
case object AndC extends HOLConst(AndSymbol, ->(To(), ->(To(), To()))) with SchemataFormula
case object OrC extends HOLConst(OrSymbol, ->(To(), ->(To(), To()))) with SchemataFormula
case object ImpC extends HOLConst(ImpSymbol, ->(To(), ->(To(), To()))) with SchemataFormula
case object BigAndC extends HOLConst(BigAndSymbol, ->(Tindex(), (->(Tindex(), (->(Tindex(), ->(->(Tindex(), To()), To())))) ))) with SchemataFormula
case object BigOrC extends HOLConst(BigOrSymbol, ->(Tindex(), (->(Tindex(), (->(Tindex(), ->(->(Tindex(), To()), To())))) ))) with SchemataFormula



object FOLSchemataFactory  {
  def createVar(s: VariableSymbolA, indexTerms: List[IntegerTermExpression], tp: TA): SchemataExpression = new IndexedPredicateVar(s, indexTerms, tp)
}
