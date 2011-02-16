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
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.hol.HOLFactory

// propositiopnal
trait Schema extends HOL {
  override def factory: LambdaFactoryA = SchemaFactory//FOLSchemataFactory
}

trait SchemaExpression extends HOLExpression with Schema


trait IntegerTerm extends SchemaExpression {
  require( exptype == Tindex() )
//  def exptype = Tindex()
//  def isPredecessorOf(i: IntegerTermExpression): Boolean = i match {
//    case
//  }
}

class IntVar (name: VariableSymbolA, dbInd: Option[Int]) extends HOLVar(name, Tindex(), dbInd) with IntegerTerm {
  override def toString = name.toString+":"+exptype.toString
}
case object IntVar {
  def apply(name: VariableSymbolA) = SchemaFactory.createVar(name).asInstanceOf[IntVar]
}

class IntConst(name: ConstantSymbolA) extends HOLConst(name, Tindex()) with IntegerTerm {
  //override def toString = "0:"+exptype
  //def toInt: Int = 0
}

object IntZero {
  def apply() = SchemaFactory.createVar(ConstantStringSymbol("0")).asInstanceOf[IntConst]
}

object Succ extends HOLConst(new ConstantStringSymbol("s"), ->(Tindex(), Tindex())) {
  override def toString = this match {
    case App(Succ, t) => "s("+t.toString+")"
    case _ => "ERROR in Succ"
  }
  def apply(t: IntegerTerm): IntegerTerm  = SchemaFactory.createApp(Succ, t).asInstanceOf[IntegerTerm]
  def unapply(p: IntegerTerm) = p match {
    case App(Succ, t : IntegerTerm) => Some(t)
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

private[schema] class SchemaAbs (variable: Var, expression: LambdaExpression)
  extends HOLAbs(variable, expression) with SchemaExpression

object SchemaAbs {
  def unapply(e: LambdaExpression) = e match {
    case Abs(v : IntVar, f: SchemaFormula) => Some(v, f)
    case _ => None
  }
}

//------------------------------------------------------------------------------------------------


/*trait IndexedPredicate(sym: ConstantSymbolA, val index: List[IntegerTerm]) extends HOLConst(sym, To(), None) with SchemataFormula {
  def arity:Int = index.size
  override def toString = {
    sym.toString+"_{"+index.foldLeft("")((x,y) => x+y.toStringSimple)+"}"
  }
} */

object IndexedPredicate {
  def apply(sym: ConstantSymbolA, indexTerms: List[IntegerTerm]): SchemaFormula = {
    val pred = SchemaFactory.createVar( sym, FunctionType( To(), indexTerms.map( a => Tindex() ) ) )
    AppN(pred, indexTerms).asInstanceOf[SchemaFormula]
  }
  /*def apply(s: ConstantSymbolA, indexTerm: LambdaExpression, tp: TA): LambdaExpression = {
    FOLSchemataFactory.createVar(s, indexTerm::Nil, tp).asInstanceOf[SchemataFormula]
  } */
}



//-------------------------------------------------------------------------------------------------

trait SchemaFormula extends SchemaExpression with HOLFormula

object Neg {
  def apply(sub: SchemaFormula) = HOLApp(NegC,sub).asInstanceOf[SchemaFormula]
  def unapply(expression: LambdaExpression) = expression match {
    case App(NegC,sub) => Some( (sub.asInstanceOf[SchemaFormula]) )
    case _ => None
  }
}

object And {
  def apply(left: SchemaFormula, right: SchemaFormula) = (SchemaFactory.createApp(SchemaFactory.createApp(AndC,left),right)).asInstanceOf[SchemaFormula]
  def unapply(expression: LambdaExpression) = expression match {
    case App(App(AndC,left),right) => Some( (left.asInstanceOf[SchemaFormula],right.asInstanceOf[SchemaFormula]) )
    case _ => None
  }
}

object Or {
  def apply(left: SchemaFormula, right: SchemaFormula) = (SchemaFactory.createApp(SchemaFactory.createApp(OrC,left),right)).asInstanceOf[SchemaFormula]
  def unapply(expression: LambdaExpression) = expression match {
    case App(App(OrC,left),right) => Some( (left.asInstanceOf[SchemaFormula],right.asInstanceOf[SchemaFormula]) )
    case _ => None
  }
}

object Imp {
  def apply(left: SchemaFormula, right: SchemaFormula) = (SchemaFactory.createApp(SchemaFactory.createApp(ImpC,left),right)).asInstanceOf[SchemaFormula]
  def unapply(expression: LambdaExpression) = expression match {
      case App(App(ImpC,left),right) => Some( (left.asInstanceOf[SchemaFormula],right.asInstanceOf[SchemaFormula]) )
      case _ => None
  }
}

object BigAnd {
  def apply(i: IntVar, iter: SchemaFormula, init: IntegerTerm, end: IntegerTerm) : SchemaFormula =
    apply(new SchemaAbs(i, iter), init, end)

  def apply(iter: SchemaAbs, init: IntegerTerm , end: IntegerTerm) : SchemaFormula =
    AppN(BigAndC, iter::init::end::Nil).asInstanceOf[SchemaFormula]
  
  def unapply(exp : LambdaExpression) = exp match {
    case AppN(BigAndC, SchemaAbs(v, formula)::(init : IntegerTerm)::(end : IntegerTerm)::Nil) =>
      Some(v, formula, init, end)
    case _ => None
  }
}

object BigOr {
  def apply(i: IntVar, iter: SchemaFormula, init: IntegerTerm, end: IntegerTerm) : SchemaFormula =
    apply(new SchemaAbs(i, iter), init, end)

  def apply(iter: SchemaAbs, init: IntegerTerm, end: IntegerTerm) : SchemaFormula =
    AppN(BigOrC, iter::init::end::Nil).asInstanceOf[SchemaFormula]

  def unapply(exp : LambdaExpression) = exp match {
    case AppN(BigOrC, SchemaAbs(v, formula)::(init : IntegerTerm)::(end : IntegerTerm)::Nil) =>
      Some(v, formula, init, end)
    case _ => None
  }
}


case object BottomC extends HOLConst(BottomSymbol, To()) with SchemaFormula
case object NegC extends HOLConst(NegSymbol, ->(To(), To())) with Schema
case object AndC extends HOLConst(AndSymbol, ->(To(), ->(To(), To()))) with Schema
case object OrC extends HOLConst(OrSymbol, ->(To(), ->(To(), To()))) with Schema
case object ImpC extends HOLConst(ImpSymbol, ->(To(), ->(To(), To()))) with Schema
// FIXME: parser cannot parse the type written in the next line
//case object BigAndC extends HOLConst(BigAndSymbol, "( ( e -> o ) -> ( e -> ( e -> o ) ) )") with Schema
case object BigAndC extends HOLConst(BigAndSymbol, ->(->(Tindex(), To()), ->(Tindex(), ->(Tindex(), To())))) with Schema
//case object BigOrC extends HOLConst(BigOrSymbol, "( ( e -> o ) -> ( e -> ( e -> o ) ) )") with Schema
case object BigOrC extends HOLConst(BigOrSymbol, ->(->(Tindex(), To()), ->(Tindex(), ->(Tindex(), To())))) with Schema


object SchemaFactory extends LambdaFactoryA {
  def createVar( name: SymbolA): Var = createVar(name, Tindex(), None)
  def createVar( name: SymbolA, exptype: TA, dbInd: Option[Int]) : Var = name match {
    case a: ConstantSymbolA if exptype == Tindex()=> new IntConst(a)
    case a: VariableSymbolA if exptype == Tindex() => new IntVar(a, dbInd)
    case a: ConstantSymbolA => new HOLConst(a, exptype) with Schema
  }
  def createAbs( variable: Var, exp: LambdaExpression ): Abs = new SchemaAbs( variable, exp )
  def createApp( fun: LambdaExpression, arg: LambdaExpression ): App = arg match {
    case a: IntegerTerm if fun == Succ => new SchemaApp(Succ, a) with IntegerTerm
    // TODO: the next line is only correct for symbols expecting exactly one index
    //case a: IntegerTerm => new SchemaApp(fun, a) with SchemaFormula
    case _ => if (HOLFactory.isFormulaWhenApplied(fun.exptype)) new SchemaApp(fun, arg) with SchemaFormula
      else new SchemaApp(fun, arg)
  }
  //private  def createPlus(t1: IntegerTermExpression, t2:IntegerTermExpression): IntegerTermExpression  = AppN(PlusC, t1::t2::Nil).asInstanceOf[IntegerTermExpression]
 // private def createTimes(t1: IntegerTermExpression, t2:IntegerTermExpression): IntegerTermExpression  = AppN(TimesC, t1::t2::Nil).asInstanceOf[IntegerTermExpression]
}
