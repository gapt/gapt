package at.logic.language.schema

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
import at.logic.language.hol.HOLFactory

// propositiopnal
trait Schema extends HOL {
  override def factory: LambdaFactoryA = SchemaFactory//FOLSchemataFactory
}

trait SchemaExpression extends HOLExpression with Schema


trait IntegerTerm extends SchemaExpression with Schema {
  require( exptype == Tindex() )
//  def exptype = Tindex()
//  def isPredecessorOf(i: IntegerTermExpression): Boolean = i match {
//    case
//  }
}

class IntVar (name: VariableSymbolA) extends HOLVar(name, Tindex(), None) with IntegerTerm {
  override def toString = name.toString+":"+exptype.toString
}
case object IntVar {
  def apply(name: VariableSymbolA) = SchemaFactory.createVar(name).asInstanceOf[IntegerTerm]//IntegerTermFactory.createVar(name)
}


class IntZero  extends HOLConst(ConstantStringSymbol("0"), Tindex()) with IntegerTerm {
  override def toString = "0:"+exptype
  def toInt: Int = 0
}

object IntZero {
  def apply() = SchemaFactory.createVar(ConstantStringSymbol("0")).asInstanceOf[IntegerTerm]
}

case object Succ extends HOLConst(new ConstantStringSymbol("s"), ->(Tindex(), Tindex())) with IntegerTerm {
  override def toString = this match {
    case App(Succ, t) => "s("+t.toString+")"
    case _ => "ERROR in Succ"
  }
  def apply(t: LambdaExpression): App  = SchemaFactory.createApp(Succ, t)
  def unapply(p: IntegerTerm) = p match {
    case App(Succ, t) => Some(t)
    case _ => None
  }
}

/*     not yet defined
case object PlusC extends HOLConst(new ConstantStringSymbol("+"), ->(Tindex(), ->(Tindex(), Tindex()))){
  def apply(t1: IntegerTermExpression, t2:IntegerTermExpression): IntegerTermExpression  = IntegerTermFactory.createPlus(t1,t2)
}

case object TimesC extends HOLConst(new ConstantStringSymbol("×"), ->(Tindex(), ->(Tindex(), Tindex()))) {
  def apply(t1: IntegerTermExpression, t2:IntegerTermExpression): IntegerTermExpression  = IntegerTermFactory.createTimes(t1,t2)
}
  */

private[schema] class SchemaApp(function: LambdaExpression, argument: LambdaExpression)
  extends HOLApp(function, argument) with SchemaExpression

//------------------------------------------------------------------------------------------------


/*trait IndexedPredicate(sym: ConstantSymbolA, val index: List[IntegerTerm]) extends HOLConst(sym, To(), None) with SchemataFormula {
  def arity:Int = index.size
  override def toString = {
    sym.toString+"_{"+index.foldLeft("")((x,y) => x+y.toStringSimple)+"}"
  }
} */

object IndexedPredicate {
  def apply(sym: ConstantSymbolA, indexTerms: List[IntegerTerm]): SchemaFormula = {
    val pred : Var = SchemaFactory.createVar( sym, FunctionType( To(), indexTerms.map( a => Tindex() ) ) )
    AppN(pred, indexTerms).asInstanceOf[SchemaFormula]
  }
  /*def apply(s: ConstantSymbolA, indexTerm: LambdaExpression, tp: TA): LambdaExpression = {
    FOLSchemataFactory.createVar(s, indexTerm::Nil, tp).asInstanceOf[SchemataFormula]
  } */
}



//-------------------------------------------------------------------------------------------------

trait SchemaFormula extends SchemaExpression {
//  def and(that: SchemataFormula) =  And(this, that)
//  def or(that: SchemataFormula) = Or(this, that)
//  def imp(that: SchemataFormula) = Imp(this, that)
//  def bigAnd(begin: IntegerTermExpression, end: IntegerTermExpression, v: IndexedPredicateVar) =  BigAnd(begin, end, v)
//  def bigOr(begin: IntegerTermExpression, end: IntegerTermExpression, v: IndexedPredicateVar) =  BigOr(begin, end, v)
}

object SNeg {
  def apply(sub: SchemaFormula) = HOLApp(NegC,sub).asInstanceOf[SchemaFormula]
  def unapply(expression: LambdaExpression) = expression match {
    case App(NegC,sub) => Some( (sub.asInstanceOf[SchemaFormula]) )
    case _ => None
  }
}

object SAnd {
  def apply(left: SchemaFormula, right: SchemaFormula) = (SchemaFactory.createApp(SchemaFactory.createApp(AndC,left),right)).asInstanceOf[SchemaFormula]
  def unapply(expression: LambdaExpression) = expression match {
    case App(App(AndC,left),right) => Some( (left.asInstanceOf[SchemaFormula],right.asInstanceOf[SchemaFormula]) )
    case _ => None
  }
}

object SOr {
  def apply(left: SchemaFormula, right: SchemaFormula) = (SchemaFactory.createApp(SchemaFactory.createApp(OrC,left),right)).asInstanceOf[SchemaFormula]
  def unapply(expression: LambdaExpression) = expression match {
    case App(App(OrC,left),right) => Some( (left.asInstanceOf[SchemaFormula],right.asInstanceOf[SchemaFormula]) )
    case _ => None
  }
}

object SImp {
  def apply(left: SchemaFormula, right: SchemaFormula) = (SchemaFactory.createApp(SchemaFactory.createApp(ImpC,left),right)).asInstanceOf[SchemaFormula]
  def unapply(expression: LambdaExpression) = expression match {
      case App(App(ImpC,left),right) => Some( (left.asInstanceOf[SchemaFormula],right.asInstanceOf[SchemaFormula]) )
      case _ => None
  }
}

object BigAnd {
  def apply(iter: IntVar, init: IntegerTerm , end: IntegerTerm, sf : SchemaFormula) =
    AppN(BigAndC, iter::init::end::sf::Nil).asInstanceOf[SchemaFormula]
}

object BigOr {
  def apply(iter: IntVar, init: IntegerTerm, end: IntegerTerm, sf : SchemaFormula) =
    AppN(BigOrC, iter::init::end::sf::Nil).asInstanceOf[SchemaFormula]
}

case object BottomC extends HOLConst(BottomSymbol, To()) with SchemaFormula
case object NegC extends HOLConst(NegSymbol, ->(To(), To())) with SchemaFormula
case object AndC extends HOLConst(AndSymbol, ->(To(), ->(To(), To()))) with SchemaFormula
case object OrC extends HOLConst(OrSymbol, ->(To(), ->(To(), To()))) with SchemaFormula
case object ImpC extends HOLConst(ImpSymbol, ->(To(), ->(To(), To()))) with SchemaFormula
case object BigAndC extends HOLConst(BigAndSymbol, ->(Tindex(), (->(Tindex(), (->(Tindex(), ->(->(Tindex(), To()), To())))) ))) with SchemaFormula
case object BigOrC extends HOLConst(BigOrSymbol, ->(Tindex(), (->(Tindex(), (->(Tindex(), ->(->(Tindex(), To()), To())))) ))) with SchemaFormula


object SchemaFactory extends LambdaFactoryA {
  def createVar( name: SymbolA): Var = createVar(name, Tindex(), None)
  def createVar( name: SymbolA, exptype: TA, dbInd: Option[Int]) : Var = name match {
    case a: ConstantSymbolA if exptype == Tindex()=> new IntZero
    case a: VariableSymbolA if exptype == Tindex() => new IntVar(a)
    case a: ConstantSymbolA => new HOLConstFormula(a) with SchemaFormula
  }
  def createAbs( variable: Var, exp: LambdaExpression ): Abs = throw new AbstractMethodError //HOLFactory.createAbs(variable, exp )
  def createApp( fun: LambdaExpression, arg: LambdaExpression ): App = arg match {
    case a: IntegerTerm if fun == Succ => new SchemaApp(Succ, a) with IntegerTerm
    case a: IntegerTerm => new SchemaApp(Succ, a) with SchemaFormula
    case _ => throw new IllegalArgumentException("Creating applications which are not integer terms or IndexedPredicate")
  }
  //private  def createPlus(t1: IntegerTermExpression, t2:IntegerTermExpression): IntegerTermExpression  = AppN(PlusC, t1::t2::Nil).asInstanceOf[IntegerTermExpression]
 // private def createTimes(t1: IntegerTermExpression, t2:IntegerTermExpression): IntegerTermExpression  = AppN(TimesC, t1::t2::Nil).asInstanceOf[IntegerTermExpression]
}
