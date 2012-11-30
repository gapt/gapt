package at.logic.language.schema

/*The definition of Indexed proposition is taken from:
 * A Schemata Calculus for Propositional Logic by Vincent Aravantinos, Ricardo Caferra, and Nicolas Peltier
 **/


import at.logic.language.lambda.types._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.symbols._
import at.logic.language.hol._
import at.logic.language.hol.logicSymbols._
import at.logic.language.schemata.logicSymbols._
import at.logic.language.lambda.types.ImplicitConverters._
import at.logic.language.hol.HOLFactory
import at.logic.language.lambda.substitutions.Substitution
import at.logic.language.hol.Definitions._
import at.logic.language.lambda.typedLambdaCalculus.Var._
import collection.immutable.HashSet

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

//trait schemaTerm extends SchemaExpression

object aTerm {
  def apply(name: HOLConst, ind: IntegerTerm): IntegerTerm = {
    SchemaFactory.createApp(name, ind).asInstanceOf[IntegerTerm]
  }
}

object foTerm {
  def apply(name: String, args: List[HOLExpression]): HOLExpression = {
    val v = hol.createVar(new VariableStringSymbol(name), args.head.exptype  -> Ti()).asInstanceOf[HOLVar]
    HOLApp(v, args.head).asInstanceOf[HOLExpression]
  }
  def apply(v: HOLVar, args: List[HOLExpression]): HOLExpression = {
    HOLApp(v, args.head).asInstanceOf[HOLExpression]
  }
  def unapply(s: HOLExpression) = s match {
    case HOLApp(v, arg) if s.exptype == Ti() => Some(v, arg)
    case _ => None
  }
}

//database for trs
object dbTRS extends Iterable[(HOLConst, Tuple2[Tuple2[HOLExpression, HOLExpression], Tuple2[HOLExpression, HOLExpression]])] {
  val map = new scala.collection.mutable.HashMap[HOLConst, Tuple2[Tuple2[HOLExpression, HOLExpression], Tuple2[HOLExpression, HOLExpression]]]
  def get(name: HOLConst) = map(name)
  def clear = map.clear
  def add(term: HOLConst, base: Tuple2[HOLExpression, HOLExpression], step: Tuple2[HOLExpression, HOLExpression]): Unit = {
    map.put(term, Tuple2(base, step))
  }
  def iterator = map.iterator
}


//TODO : needs improvement for the step case
object unfoldSTerm {
  def apply(t: HOLExpression): HOLExpression = {
    val k = IntVar(new VariableStringSymbol("k"))
    val x = foVar("x")
//    println("\nunfoldSTerm = "+t)
//    println("trs : "+dbTRS.map)
    t match {
      case sTerm(func, i, arg) if dbTRS.map.contains(func.asInstanceOf[HOLConst]) => {
//        println("sTerm, i = "+i)
        if (i == IntZero()) {
//          println("i == IntZero()")
          val base = dbTRS.map.get(func.asInstanceOf[HOLConst]).get._1._2
          val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(x, arg.head)
          val subst = new SchemaSubstitution2[HOLExpression](new_map)
          subst(base)
        }
        else
          if (i == k)
            t
          else
            i match {
              case Succ(_) => {
//                println("case Succ(_)")
                dbTRS.map.get(func.asInstanceOf[HOLConst]).get._2._2 match {
                  case foTerm(name, arg1) => {
                    //                println("i = "+i)

                    val rez = foTerm(name.asInstanceOf[HOLVar], apply(sTerm(func.asInstanceOf[HOLConst], Pred(i.asInstanceOf[IntegerTerm]), arg))::Nil)
//                    println("rez = "+rez)
                    rez
                  }
                }
              }
              case _ => {
//                println("m(.)")
                  val j = unfoldSINDTerm(i)
//                  println("j = "+j)
                  val rez = apply(sTerm(func.asInstanceOf[HOLConst], j, arg))
//                  println("rez = "+rez)
                  rez
                }
              }
      }
      case sTerm(func, i, arg) => {
//        println("sTerm BAD")
        t
      }
      case foTerm(holvar, arg) => {
//        println("foTerm = "+t)
        foTerm(holvar.asInstanceOf[HOLVar], apply(arg)::Nil)
      }
      case _ => t//throw new Exception("\nno such case in schema/unfoldSTerm")
    }
  }
}

object unfoldSINDTerm {
  def apply(t: HOLExpression): HOLExpression = {
//    println("\nunfoldSINDTerm")
//    println("trs : "+dbTRS.map)
    val k = IntVar(new VariableStringSymbol("k"))
    t match {
      case sIndTerm(func, i) if dbTRS.map.contains(func.asInstanceOf[HOLConst]) => {
//        println("sIndTerm = "+t)
        if (i == IntZero()) {
          val base = dbTRS.map.get(func.asInstanceOf[HOLConst]).get._1._2
          base
          //          val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(x, arg.head)
          //          val subst = new SchemaSubstitution2[HOLExpression](new_map)
          //          subst(base)
        }
        else
        if (i == k)
          t
        else {
          val step = dbTRS.map.get(func.asInstanceOf[HOLConst]).get._2._2
          val new_map = scala.collection.immutable.Map[Var, HOLExpression]() + Pair(k, Pred(i.asInstanceOf[IntegerTerm]))
          val subst = new SchemaSubstitution2[HOLExpression](new_map)
          subst(step)
        }
      }
      case _ => {
//        println("case _ => ")
        t
      }//throw new Exception("\nno such case in schema/unfoldSTerm")
    }
  }
}


object unfoldSFormula {
  def apply(f: HOLFormula): HOLFormula = {
//    println("\nnunfolding formula : "+f)
    f match {
      //case IndexedPredicate(pointer @ f, l @ ts) => IndexedPredicate(pointer.name.asInstanceOf[ConstantSymbolA], apply(l.head.asInstanceOf[T]).asInstanceOf[IntegerTerm]).asInstanceOf[T]
      case Atom(name, args) => {
        val ff = Atom(name, args.map(t => unfoldSTerm(t)))
//        println("ff = "+ff)
        ff
      }
      case Imp(f1, f2) => Imp(apply(f1.asInstanceOf[HOLFormula]), apply(f2.asInstanceOf[HOLFormula]))
      case ExVar(v, f) => ExVar(v, apply(f))
      case AllVar(v, f) => AllVar(v, apply(f))
//      case BigAnd(v, formula, init, end) => BigAnd(v, formula, apply(init.asInstanceOf[T]).asInstanceOf[IntegerTerm], apply(end.asInstanceOf[T]).asInstanceOf[IntegerTerm] ).asInstanceOf[T]
//      case BigOr(v, formula, init, end) =>   BigOr(v, formula, apply(init.asInstanceOf[T]).asInstanceOf[IntegerTerm], apply(end.asInstanceOf[T]).asInstanceOf[IntegerTerm] ).asInstanceOf[T]
//      case Succ(n) => Succ(apply(n.asInstanceOf[T]).asInstanceOf[IntegerTerm]).asInstanceOf[T]
//      case Or(l @ left, r @ right) => Or(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula], apply(r.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]
//      case And(l @ left, r @ right) => And(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula], apply(r.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]
//      case Neg(l @ left) => Neg(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]
      case _ => f

    }
  }
}

object sTerm {
  //the i should be of type Tindex() !
  def apply(f: String, i: HOLExpression, l: List[HOLExpression]): HOLExpression = {
    require(i.exptype == Tindex())
//    AppN(HOLConst(new ConstantStringSymbol(f), ->(Tindex() , ->(Ti(), Ti()))), i::l).asInstanceOf[schemaTerm]
    if(l.isEmpty) {
      val func = HOLConst(new ConstantStringSymbol(f), ->(Tindex() , Ti()))
      return HOLApp(func, i).asInstanceOf[HOLExpression]
    }
    else {
      val func = HOLConst(new ConstantStringSymbol(f), ->(Tindex() , ->(Ti(), Ti())))
      return HOLApp(HOLApp(func, i), l.head).asInstanceOf[HOLExpression]
    }
  }
  def apply(f: HOLConst, i: HOLExpression, l: List[HOLExpression]): HOLExpression = {
    require(i.exptype == Tindex())
    if(l.isEmpty)
      HOLApp(f, i).asInstanceOf[HOLExpression]
    else
      HOLApp(HOLApp(f, i), l.head).asInstanceOf[HOLExpression]
  }
  def unapply(s : HOLExpression) = s match {
    case HOLApp(HOLApp(func, i), arg) if i.exptype == Tindex() => Some( ( func, i, arg::Nil ) )
    case HOLApp(func, i) if i.exptype == Tindex() => Some( ( func, i, Nil ) )
    //Should remain only this one if it is OK
//    case Function(name, args, typ) if typ == Ti() && args.head.exptype == Tindex() => {
//      val typ = args.map(x => x.exptype).foldLeft(Ti().asInstanceOf[TA])((x,t) => ->(x, t))
//      val f = HOLConst(name.asInstanceOf[ConstantStringSymbol], typ)
//      Some((f.name.toString(), args.head.asInstanceOf[HOLExpression], args.tail.asInstanceOf[List[HOLExpression]]))
//    }
    case _ => None
  }
}

//indexed s-term of type ω->ω
object sIndTerm {
  //the i should be of type Tindex() !
  def apply(f: String, i: IntegerTerm): HOLExpression = {
    val func = HOLConst(new ConstantStringSymbol(f), ->(Tindex() , Tindex()))
    return HOLApp(func, i).asInstanceOf[HOLExpression]
  }
  def unapply(s : HOLExpression) = s match {
    case HOLApp(func, i) if i.exptype == Tindex() => Some( ( func.asInstanceOf[HOLConst], i) )
    case _ => None
  }
}


class sTermRewriteSys(val func: HOLConst, val base: HOLExpression, val rec: HOLExpression) {
}

object sTermRewriteSys {
  def apply(f: HOLConst, base: HOLExpression, step: HOLExpression) = new sTermRewriteSys(f, base, step)
}

object sTermDB extends Iterable[(HOLConst, sTermRewriteSys)] with TraversableOnce[(HOLConst, sTermRewriteSys)] {
  val terms = new scala.collection.mutable.HashMap[HOLConst, sTermRewriteSys]
  def clear = terms.clear
  def get(func: HOLConst) = terms(func)
  def put(sterm: sTermRewriteSys) = terms.put(sterm.func, sterm)
  def iterator = terms.iterator
}

class IntVar (name: VariableSymbolA, dbInd: Option[Int]) extends HOLVar(name, Tindex(), dbInd) with IntegerTerm {
  override def toString = name.toString+":"+exptype.toString
}
case object IntVar {
  def apply(name: VariableSymbolA) = SchemaFactory.createVar(name).asInstanceOf[IntVar]
  def unapply(t: IntegerTerm) = t match {
    case v:HOLVar => Some(t)
    case _ => None
  }
}

class IntConst(name: ConstantSymbolA) extends HOLConst(name, Tindex()) with IntegerTerm {
  //override def toString = "0:"+exptype
  //def toInt: Int = 0
}


case class IntZero() extends HOLConst(ConstantStringSymbol("0"), Tindex()) with IntegerTerm

//object IntZero {
//  def apply() = SchemaFactory.createVar(ConstantStringSymbol("0")).asInstanceOf[IntConst]
//}

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

//  Predecessor, the inverse of successor Succ
object Pred {
  def apply(t: IntegerTerm): IntegerTerm  =  {
//    println("Pred : "+t)
    t match {
      case Succ(t1) => t1
//      case z:IntZero => t
//      case IntVar(v) => t
      case _ => throw new Exception("ERROR in Predecessor")
    }
  }
  /*def unapply(p: IntegerTerm) = p match {
    case App(Succ, t : IntegerTerm) => Some(t)
    case _ => None
  } */
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
  def apply(sym: ConstantSymbolA, indexTerm: IntegerTerm): SchemaFormula = apply(sym, indexTerm::Nil)

  def unapply(e: LambdaExpression) = e match {
    case AppN(f : HOLConst with Schema, ts) if ts.forall( t => t.exptype == Tindex() ) && e.exptype == To() => Some((f, ts))
    case _ => None
  }
}



//-------------------------------------------------------------------------------------------------

trait SchemaFormula extends SchemaExpression with HOLFormula {
  // Re-implemented here because of the IndexedPredicate case
  override def isAtom : Boolean = this match {
    case Atom(_,_) => true
    case IndexedPredicate(_,_) => true
    case _ => false
  }
}

object BiggerThan {
  def apply(l: IntegerTerm, r: IntegerTerm) = Atom(BiggerThanC, l::r::Nil)

  def unapply(e: LambdaExpression) = e match {
    case AppN(BiggerThanC, l::r::Nil) => Some((l.asInstanceOf[SchemaFormula], r.asInstanceOf[SchemaFormula]))
    case _ => None
  }
}

object Neg {
  def apply(sub: SchemaFormula) = App(NegC,sub).asInstanceOf[SchemaFormula]
  def unapply(expression: LambdaExpression) = expression match {
//    case App(NegC,sub) => Some( (sub.asInstanceOf[SchemaFormula]) )
    case App(NegC,sub) => Some( sub )

    case _ => None
  }
}

object And {
  def apply(left: SchemaFormula, right: SchemaFormula) = (SchemaFactory.createApp(SchemaFactory.createApp(AndC,left),right)).asInstanceOf[SchemaFormula]
  def unapply(expression: LambdaExpression) = expression match {
    case App(App(AndC,left),right) => Some( (left,right) )
    case _ => None
  }
}

object Or {
  def apply(left: SchemaFormula, right: SchemaFormula) = (SchemaFactory.createApp(SchemaFactory.createApp(OrC,left),right)).asInstanceOf[SchemaFormula]

  def apply(fs: List[SchemaFormula]) : SchemaFormula = fs match {
    case Nil => BottomC
    case f::fs => fs.foldLeft(f)( (d, f) => Or(d, f) )
  }

  def unapply(expression: LambdaExpression) = expression match {
    case App(App(OrC,left),right) => Some( (left,right) )
    case _ => None
  }
}

object Imp {
  def apply(left: HOLFormula, right: HOLFormula) = (SchemaFactory.createApp(SchemaFactory.createApp(ImpC,left),right)).asInstanceOf[SchemaFormula]
  def unapply(expression: LambdaExpression) = expression match {
      case App(App(ImpC,left),right) => Some( (left,right) )
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

// This factory creates a formula that
// is true iff param = 0
object isZero {
  def apply(param: IntegerTerm) =
    BigAnd( IntVar(new VariableStringSymbol("i")), BottomC, Succ(IntZero()), param )
}

// This factory creates a formula that
// is true iff x > y
object isBiggerThan {
  def apply(x: IntegerTerm, y: IntegerTerm) =
    BigAnd( IntVar(new VariableStringSymbol("i")), BottomC, x, y )
}

case object BottomC extends HOLConst(BottomSymbol, To()) with SchemaFormula
case object TopC extends HOLConst(BottomSymbol, To()) with SchemaFormula
case object NegC extends HOLConst(NegSymbol, ->(To(), To())) with Schema
case object AndC extends HOLConst(AndSymbol, ->(To(), ->(To(), To()))) with Schema
case object OrC extends HOLConst(OrSymbol, ->(To(), ->(To(), To()))) with Schema
case object ImpC extends HOLConst(ImpSymbol, ->(To(), ->(To(), To()))) with Schema

// Schema-specific objects
// FIXME: parser cannot parse the type written in the next line
//case object BigAndC extends HOLConst(BigAndSymbol, "( ( e -> o ) -> ( e -> ( e -> o ) ) )") with Schema
case object BigAndC extends HOLConst(BigAndSymbol, ->(->(Tindex(), To()), ->(Tindex(), ->(Tindex(), To())))) with Schema
//case object BigOrC extends HOLConst(BigOrSymbol, "( ( e -> o ) -> ( e -> ( e -> o ) ) )") with Schema
case object BigOrC extends HOLConst(BigOrSymbol, ->(->(Tindex(), To()), ->(Tindex(), ->(Tindex(), To())))) with Schema

// Helpers to represent preconditions in construction of characteristic clause
// set
// TODO: determine what these mean in the official language of "A Resolution
// Calculus for Propositional Schemata"
case object BiggerThanSymbol extends ConstantSymbolA {
  override def unique = "BiggerThanSymbol"
  override def toString = ">"
  def toCode = "BiggerThanSymbol"

  def compare(that: SymbolA) = that match {
    case a: ConstantSymbolA => unique.compare( a.unique )
  }
}

case object BiggerThanC extends HOLConst(BiggerThanSymbol, ->(Tindex(), ->(Tindex(), To()))) with Schema

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

//this substitution works for IntVar Only. It gives an instance of a schema.
class SchemaSubstitution[T <: HOLExpression](map: scala.collection.immutable.Map[Var, T]) extends Substitution[T](map) {
   override def applyWithChangeDBIndices(expression: T, protectedVars: List[Var]): T = expression match {
      case x:IntVar if !(protectedVars.contains(x)) => {
          map.get(x) match {
            case Some(t) => {
              //println("substituting " + t.toStringSimple + " for " + x.toStringSimple)
              t
            }
            case None => {
              //println(x + " is free, but we don't substitute for it")
              x.asInstanceOf[T]
            }
        }
      }
      case x:IntVar => {
        if (map.contains( x ) )
          println("WARNING: trying to substitute for a bound variable, ignoring!")
       expression
      }
      case App(m,n) => App(applyWithChangeDBIndices(m.asInstanceOf[T], protectedVars), applyWithChangeDBIndices(n.asInstanceOf[T], protectedVars)).asInstanceOf[T]
      case abs: Abs => Abs(abs.variable, applyWithChangeDBIndices(abs.expressionInScope.asInstanceOf[T], abs.variable::protectedVars)).asInstanceOf[T]
      case _ => expression
  }
}

class indexedFOVar(override val name: VariableStringSymbol, val index: IntegerTerm) extends HOLVar(name, Ti(), None) {
  override def toString = name.toString+"("+index+")"+":"+exptype.toString
  override def equals(a: Any): Boolean = a match {
    case v:indexedFOVar if v.name.toString() == this.name.toString() && v.index == this.index => true
    case _ => false
  }
}

object indexedFOVar {
  def apply(name: VariableStringSymbol, i: IntegerTerm): HOLVar = {
    new indexedFOVar(name, i)
  }
  def unapply(s: HOLExpression) = s match {
    case v: indexedFOVar => Some(v.name, v.index)
    case _ => None
  }
}

class foVar(name: VariableStringSymbol) extends HOLVar(name, Ti(), None) {
  override def equals(a: Any): Boolean = a match {
    case v:foVar if v.name.toString() == this.name.toString() => true
    case _ => false
  }
}
object foVar{
  def apply(name: String) = (new foVar(new VariableStringSymbol(name))).asInstanceOf[HOLVar]
  def unapply(t: HOLExpression) = t match {
    case HOLVar(name, typ) => Some(name, typ)
    case _ => None
  }
}

class SchemaSubstitution1[T <: HOLExpression](val map: scala.collection.immutable.Map[Var, T])  {
  def apply(expression: T): T = expression match {
    case x:IntVar => {
//      println("\nIntVar = "+x)
      map.get(x) match {
        case Some(t) => {
//          println("substituting " + t.toStringSimple + " for " + x.toStringSimple)
          t
        }
        case _ => {
//          println(x + " Error in schema subst 1")
          x.asInstanceOf[T]
        }
      }
    }
    case IndexedPredicate(pointer @ f, l @ ts) => IndexedPredicate(pointer.name.asInstanceOf[ConstantSymbolA], apply(l.head.asInstanceOf[T]).asInstanceOf[IntegerTerm]).asInstanceOf[T]
    case BigAnd(v, formula, init, end) => BigAnd(v, formula, apply(init.asInstanceOf[T]).asInstanceOf[IntegerTerm], apply(end.asInstanceOf[T]).asInstanceOf[IntegerTerm] ).asInstanceOf[T]
    case BigOr(v, formula, init, end) =>   BigOr(v, formula, apply(init.asInstanceOf[T]).asInstanceOf[IntegerTerm], apply(end.asInstanceOf[T]).asInstanceOf[IntegerTerm] ).asInstanceOf[T]
    case Succ(n) => Succ(apply(n.asInstanceOf[T]).asInstanceOf[IntegerTerm]).asInstanceOf[T]
    case Or(l @ left, r @ right) => Or(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula], apply(r.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]
    case And(l @ left, r @ right) => And(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula], apply(r.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]
    case Neg(l @ left) => Neg(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]
    case Imp(l, r) => Imp(apply(l.asInstanceOf[T]).asInstanceOf[HOLFormula], apply(r.asInstanceOf[T]).asInstanceOf[HOLFormula]).asInstanceOf[T]
    case AllVar(v, f) => AllVar(v, apply(f.asInstanceOf[T]).asInstanceOf[HOLFormula]).asInstanceOf[T]
    case at @ Atom(name, args) => {
      Atom(name, args.map(x => apply(x.asInstanceOf[T]).asInstanceOf[HOLExpression])).asInstanceOf[T]
    }
    case ifo: indexedFOVar => indexedFOVar(ifo.name, apply(ifo.index.asInstanceOf[T]).asInstanceOf[IntegerTerm]).asInstanceOf[T]
    case st @ sTerm(name, i, args) => {
      sTerm(name.asInstanceOf[HOLConst], apply(i.asInstanceOf[T]).asInstanceOf[IntegerTerm], args.map(x => apply(x.asInstanceOf[T]))).asInstanceOf[T]
    }
    case foTerm(v, arg) => foTerm(v.asInstanceOf[HOLVar], apply(arg.asInstanceOf[T])::Nil).asInstanceOf[T]
    case _ => {
//      println("\n SchemaSubstitution1: case _ => " + expression.toString + " : "+expression.getClass)
      expression
    }
  }
/*
  def apply(fseq: FSequent): FSequent = {
    FSequent(fseq._1.map(f => apply(f.asInstanceOf[T]).asInstanceOf[HOLFormula]),fseq._2.map(f => apply(f.asInstanceOf[T]).asInstanceOf[HOLFormula]))
  }
*/
}

class SchemaSubstitution2[T <: HOLExpression](val map: scala.collection.immutable.Map[Var, T])  {
  def apply(expression: T): T = {
//    println("subst")
    expression match {
      case x:IntVar => {
        //      println("\nIntVar = "+x)
        map.get(x) match {
          case Some(t) => {
            //          println("substituting " + t.toStringSimple + " for " + x.toStringSimple)
            t
          }
          case _ => {
            //          println(x + " Error in schema subst 1")
            x.asInstanceOf[T]
          }
        }
      }
      case x:foVar => {
//        println("\nfoVar = "+x)
        map.get(x) match {
          case Some(t) => {
            //          println("substituting " + t.toStringSimple + " for " + x.toStringSimple)
            t
          }
          case _ => {
            //          println(x + " Error in schema subst 1")
            x.asInstanceOf[T]
          }
        }
      }
      case IndexedPredicate(pointer @ f, l @ ts) => IndexedPredicate(pointer.name.asInstanceOf[ConstantSymbolA], apply(l.head.asInstanceOf[T]).asInstanceOf[IntegerTerm]).asInstanceOf[T]
      case BigAnd(v, formula, init, end) => BigAnd(v, formula, apply(init.asInstanceOf[T]).asInstanceOf[IntegerTerm], apply(end.asInstanceOf[T]).asInstanceOf[IntegerTerm] ).asInstanceOf[T]
      case BigOr(v, formula, init, end) =>   BigOr(v, formula, apply(init.asInstanceOf[T]).asInstanceOf[IntegerTerm], apply(end.asInstanceOf[T]).asInstanceOf[IntegerTerm] ).asInstanceOf[T]
      case Succ(n) => Succ(apply(n.asInstanceOf[T]).asInstanceOf[IntegerTerm]).asInstanceOf[T]
      case Or(l @ left, r @ right) => Or(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula], apply(r.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]
      case And(l @ left, r @ right) => And(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula], apply(r.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]
      case Neg(l @ left) => Neg(apply(l.asInstanceOf[T]).asInstanceOf[SchemaFormula]).asInstanceOf[T]
      case Imp(l, r) => Imp(apply(l.asInstanceOf[T]).asInstanceOf[HOLFormula], apply(r.asInstanceOf[T]).asInstanceOf[HOLFormula]).asInstanceOf[T]
      case AllVar(v, f) => AllVar(v, apply(f.asInstanceOf[T]).asInstanceOf[HOLFormula]).asInstanceOf[T]
      case at @ Atom(name, args) => {
        Atom(name, args.map(x => apply(x.asInstanceOf[T]).asInstanceOf[HOLExpression])).asInstanceOf[T]
      }
      case ifo: indexedFOVar => indexedFOVar(ifo.name, apply(ifo.index.asInstanceOf[T]).asInstanceOf[IntegerTerm]).asInstanceOf[T]
      case st @ sTerm(name, i, args) => {
        sTerm(name.asInstanceOf[HOLConst], apply(i.asInstanceOf[T]).asInstanceOf[IntegerTerm], apply(args.asInstanceOf[T])::Nil).asInstanceOf[T]
      }
      case foTerm(v, arg) => foTerm(v.asInstanceOf[HOLVar], apply(arg.asInstanceOf[T])::Nil).asInstanceOf[T]
      case sIndTerm(func, i) => {
        sIndTerm(func.toString, apply(i.asInstanceOf[T]).asInstanceOf[IntegerTerm]).asInstanceOf[T]
      }
      case _ => {
        //      println("\ncase _ =>")
        //      println(expression)
        expression
      }
    }
  }
}
