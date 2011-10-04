/*
 * fol.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */
package at.logic.language.fol

import _root_.at.logic.language.hol.EqC._
import _root_.at.logic.language.lambda.substitutions.Substitution
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.hol.{Neg => HOLNeg, Or => HOLOr, And => HOLAnd, Imp => HOLImp, Atom => HOLAtom, Function => HOLFunction}
import at.logic.language.hol.{HOLExpression, HOL, HOLFormula, HOLVar, HOLConst, HOLApp, HOLAbs, HOLConstFormula, HOLFactory, HOLAppFormula}
import at.logic.language.hol.{AllQ => HOLAllQ, ExQ => HOLExQ, ExVar => HOLExVar, AllVar => HOLAllVar}
import at.logic.language.lambda.symbols._
import at.logic.language.lambda.types._
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.types.ImplicitConverters._
import collection.immutable.Seq

object Definitions { def fol = FOLFactory }

trait FOL extends HOL
{
  override def factory : LambdaFactoryA = FOLFactory
}

// right now FOLExpression refers to both valid FOL terms and formulas and components of such valid terms and formulas, so for example, the head symbol of an atom is also a fol expression although it has a complex type.
// we need to separate fol expression into FOLExpression which refers only to valid fol expressions and to FOLComponent which contains the fol factory but refers to possibly invlaid fol expressions.
trait FOLExpression extends HOLExpression with FOL {
    override def toString = this match {
      case Var(x,_) => x.toString
      case Atom(x, args) => x + "(" +
        (if (args.size > 1) args.head.toString + args.tail.foldLeft("")((s,a) => s+", "+a.toString)
        else args.foldLeft("")((s,a) => s+a.toString)) + ")"
      case Function(x, args) => x + "(" +
        (if (args.size > 1) args.head.toString + args.tail.foldLeft("")((s,a) => s+", "+a.toString)
        else args.foldLeft("")((s,a) => s+a.toString)) + ")"
      case And(x,y) => "(" + x.toString + AndSymbol + y.toString + ")"
      case Or(x,y) => "(" + x.toString + OrSymbol + y.toString + ")"
      case Imp(x,y) => "(" + x.toString + ImpSymbol + y.toString + ")"
      case Neg(x) => NegSymbol + x.toString
      case ExVar(x,f) => ExistsSymbol + x.toString + "." + f.toString
      case AllVar(x,f) => ForallSymbol + x.toString + "." + f.toString
      case _ => throw new Exception("Unknown FOL expression: " + super.toString)
    }

    // this function outputs the string which creates
    // an object like this. can be used to create
    // tests based on bugs.
    def toCode : String = this match {
      case FOLVar(x) => "FOLVar( " + x.toCode + " )"
      case FOLConst(x) => "FOLConst( " + x.toCode + " )"
      case Atom(x, args) => "Atom( " + x.toCode + ", " + args.foldLeft( "Nil" )( (s, a) => a.toCode + "::" + s ) + ")"
      case Function(x, args) => "Function( " + x.toCode + ", " + args.foldLeft( "Nil" )( (s, a) => a.toCode + "::" + s ) + ")"
      case And(x,y) => "And(" + x.toCode + ", " + y.toCode + ")"
      case Or(x,y) => "Or(" + x.toCode + ", " + y.toCode + ")"
      case Imp(x,y) => "Imp(" + x.toCode + ", " + y.toCode + ")"
      case Neg(x) => "Neg(" + x.toCode + ")"
      case ExVar(x,f) => "ExVar(" + x.toCode + ", " + f.toCode + ")"
      case AllVar(x,f) => "AllVar(" + x.toCode + ", " + f.toCode + ")"
      //case HArray(f1, f2) => "HArray(" + f1.toCode + ", " + f2.toCode + ")"
    }
  }
trait FOLFormula extends FOLExpression with HOLFormula
//trait FOLFormula extends HOLFormula with FOL
// the companion object converts HOL formulas into fol if the hol version has fol type
object FOLFormula {
 def apply(f: HOLFormula): FOLFormula = f match {
   case HOLNeg(x) => Neg(FOLFormula(x))
   case HOLOr(x,y) => Or(FOLFormula(x), FOLFormula(y))
   case HOLAnd(x,y) => And(FOLFormula(x), FOLFormula(y))
   case HOLImp(x,y) => Imp(FOLFormula(x), FOLFormula(y))
   case HOLAtom(nm: ConstantSymbolA, ls) if ls.forall(_.isInstanceOf[HOLExpression]) => Atom(nm, ls.map(x => FOLTerm(x.asInstanceOf[HOLExpression])))
   case HOLExVar(HOLVar(n,t),s) if (t == Ti()) => ExVar(FOLVar(n), FOLFormula(s))
   case HOLAllVar(HOLVar(n,t),s) if (t == Ti()) => AllVar(FOLVar(n), FOLFormula(s))
   case _ => throw new IllegalArgumentException("Cannot extract FOLFormula from higher order epxression: " + f.toString)
 }
}

trait FOLTerm extends FOLExpression
// trait FOLTerm extends HOLExpression with FOL
{
  require( exptype == Ti() )
}
object FOLTerm {
  def apply(t: HOLExpression): FOLTerm = t match {
    case HOLVar(n,t) if (t == Ti()) => FOLVar(n)
    case HOLConst(n,t) if (t == Ti()) => FOLConst(n)
    case HOLFunction(name: ConstantSymbolA, ls, t) if (ls.forall(_.isInstanceOf[HOLExpression])) => Function(name, ls.map(x => FOLTerm(x.asInstanceOf[HOLExpression])))
    case _ => throw new IllegalArgumentException("Cannot extract FOLTerm from higher order epxression: " + t.toString)
  }
}

// individual variable
class FOLVar (name: VariableSymbolA, dbInd: Option[Int])
  extends HOLVar(name, Ti(), dbInd) with FOLTerm

// individual constant
class FOLConst (name: ConstantSymbolA)
  extends HOLConst(name, Ti()) with FOLTerm

protected[fol] class FOLApp(function: LambdaExpression, argument: LambdaExpression)
  extends HOLApp(function, argument) with FOLExpression

protected[fol] class FOLAbs(variable: FOLVar, expression: LambdaExpression)
  extends HOLAbs(variable, expression) with FOLExpression

protected[fol] object FOLAbs {
  def apply(variable: FOLVar, expression: LambdaExpression) = new FOLAbs(variable, expression)
}

object FOLVar {
  def apply(name: VariableSymbolA) = new FOLVar(name,None)
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


object Equation {
    def apply(left: FOLTerm, right: FOLTerm) = {
      App(App(EqC, left),right).asInstanceOf[FOLFormula]
    }
    def unapply(expression: LambdaExpression) = expression match {
        case App(App(EqC,left),right) => Some( left,right )
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
    case AppN( Var( name: ConstantSymbolA, t ), args ) if t == FunctionType( To(), args.map( a => Ti() ) ) => Some( ( name, args.asInstanceOf[List[FOLTerm]] ) )
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
    case AppN( Var( name: ConstantSymbolA, t), args ) if t == FunctionType( Ti(), args.map( a => Ti() ) ) => Some( (name, args.asInstanceOf[List[FOLTerm]] ) )
    case _ => None
  }
}

case object BottomC extends HOLConst(BottomSymbol, "o") with FOLFormula
case object NegC extends HOLConst(NegSymbol, "(o -> o)") with FOL
case object AndC extends HOLConst(AndSymbol, "(o -> (o -> o))") with FOL
case object OrC extends HOLConst(OrSymbol, "(o -> (o -> o))") with FOL
case object ImpC extends HOLConst(ImpSymbol, "(o -> (o -> o))") with FOL
case object EqC extends HOLConst(EqSymbol, "(i -> (i -> o))") with FOL
class ExQ(e:TA) extends HOLExQ(e) with FOL
class AllQ(e:TA) extends HOLAllQ(e) with FOL


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

object Neg {
  def apply(sub: FOLFormula) = App(NegC,sub).asInstanceOf[FOLFormula]
  def unapply(expression: LambdaExpression) = expression match {
    case App(NegC,sub) => Some( (sub.asInstanceOf[FOLFormula]) )
    case _ => None
  }
}

object And {
  def apply(left: FOLFormula, right: FOLFormula) = (App(App(AndC,left),right)).asInstanceOf[FOLFormula]
  def unapply(expression: LambdaExpression) = expression match {
    case App(App(AndC,left),right) => Some( (left.asInstanceOf[FOLFormula],right.asInstanceOf[FOLFormula]) )
    case _ => None
  }
}

object Or {
    def apply(fs: Seq[FOLFormula]) : FOLFormula = fs match {
      case Nil => BottomC
      case f::fs => fs.foldLeft(f)( (d, f) => Or(d, f) )
    }
  def apply(left: FOLFormula, right: FOLFormula) = App(App(OrC,left),right).asInstanceOf[FOLFormula]
  def unapply(expression: LambdaExpression) = expression match {
    case App(App(OrC,left),right) => Some( (left.asInstanceOf[FOLFormula],right.asInstanceOf[FOLFormula]) )
    case _ => None
  }
}

object Imp {
  def apply(left: FOLFormula, right: FOLFormula) = App(App(ImpC,left),right).asInstanceOf[FOLFormula]
  def unapply(expression: LambdaExpression) = expression match {
      case App(App(ImpC,left),right) => Some( (left.asInstanceOf[FOLFormula],right.asInstanceOf[FOLFormula]) )
      case _ => None
  }
}


private[fol] object Ex {
  def apply(sub: LambdaExpression) = App(new ExQ(sub.exptype),sub).asInstanceOf[FOLFormula]
  def unapply(expression: LambdaExpression) = expression match {
    case App(ExQ(t),sub) => Some( (sub, t) )
    case _ => None
  }
}

private[fol] object All {
  def apply(sub: LambdaExpression) = App(new AllQ(sub.exptype),sub).asInstanceOf[FOLFormula]
  def unapply(expression: LambdaExpression) = expression match {
    case App(AllQ(t),sub) => Some( (sub, t) )
    case _ => None
  }
}

object ExVar {
  def apply(variable: FOLVar, sub: FOLFormula) = Ex(FOLAbs(variable, sub))
  def unapply(expression: LambdaExpression) = expression match {
    case Ex(Abs(variable: FOLVar, sub: FOLFormula), _) => Some( (variable, sub) )
    case _ => None
  }
}

object AllVar {
  def apply(variable: FOLVar, sub: FOLFormula) = All(FOLAbs(variable, sub))
  def unapply(expression: LambdaExpression) = expression match {
    case All(Abs(variable: FOLVar, sub: FOLFormula), _) => Some( (variable, sub) )
    case _ => None
  }
}

object ExVarInScope {
  def apply(variable: FOLVar, sub: FOLFormula) = Ex(FOLAbs(variable, sub))
  def unapply(expression: LambdaExpression) = expression match {
    case Ex(AbsInScope(variable: FOLVar, sub: FOLFormula), _) => Some( (variable, sub) )
    case _ => None
  }
}

object AllVarInScope {
  def apply(variable: FOLVar, sub: FOLFormula) = All(FOLAbs(variable, sub))
  def unapply(expression: LambdaExpression) = expression match {
    case All(AbsInScope(variable: FOLVar, sub: FOLFormula), _) => Some( (variable, sub) )
    case _ => None
  }
}

object BinaryLogicSymbol {
  def unapply(expression: LambdaExpression) = expression match {
    case And(l, r) => Some( (AndC, l, r) )
    case Or(l, r) => Some( (OrC, l, r) )
    case Imp(l, r) => Some( (ImpC, l, r) )
    case _ => None
  }
}

object FOLFactory extends LambdaFactoryA {
  import at.logic.language.fol.Utils._

  def createVar( name: SymbolA, exptype: TA, dbInd: Option[Int] ) : Var = exptype match {
    case Ti() => name match {
      case a: ConstantSymbolA => FOLConst(a)
      case a: VariableSymbolA => new FOLVar(a,dbInd)
    }
    case To() => name match {
      case a: ConstantSymbolA => new HOLConstFormula(a) with FOLFormula
      case _ => throw new Exception("In FOL, of type 'o' only constants may be created.")
    }
    case ->(tr, ta) => {
      if (!(isFirstOrderType(exptype)))
        throw new Exception("In FOL, cannot create a symbol of type " + exptype)
      name match {
        case a: ConstantSymbolA => new HOLConst(a, exptype) with FOLExpression
        case _ => throw new Exception("In FOL, of type 'a -> b' only constants may be created.")
      }
    }
  }

  def createVar( name: SymbolA ) : Var = createVar( name, Ti() )

  def createApp( fun: LambdaExpression, arg: LambdaExpression ) : App =
    if (HOLFactory.isFormulaWhenApplied(fun.exptype)) new HOLAppFormula(fun, arg) with FOLFormula
    else if (isTermWhenApplied(fun.exptype)) new FOLApp(fun, arg) with FOLTerm
    else new FOLApp(fun, arg)

  def createAbs( variable: Var, exp: LambdaExpression ) : Abs =  new HOLAbs( variable, exp ) with FOLExpression

  private def isTermWhenApplied(typ: TA) = typ match {
    case ->(_,Ti()) => true
    case _ => false
  }

}

object getFreeVariablesFOL {
  def apply( f: FOLFormula ) = f.getFreeAndBoundVariables._1.asInstanceOf[Set[FOLVar]]
}

object Utils {
  // universally closes off the given fol formula
  def universal_closure_of(f : FOLFormula) : FOLFormula = {
    val free_vars = getFreeVariablesFOL(f)
    free_vars.foldRight(f)((v : FOLVar, f : FOLFormula) => AllVar(v,f))
  }

  // this is nearly the same as LambdaExpression.getFreeAndBoundVariables, but returns the variabes in the order encountered
  def freevars_boundvars_constants_of(expression: LambdaExpression):Tuple3[List[Var],List[Var],List[Var]] = expression match {
    case v: Var if v.isFree && v.name.isInstanceOf[VariableSymbolA]=> (List(v), List(), List())
    case v: Var if v.name.isInstanceOf[VariableSymbolA] => (List(), List(v), List())
    case v: Var if v.name.isInstanceOf[ConstantSymbolA] => (List(), List(), List(v))
    case v: Var => (List(), List(), List())// not variables (constants in this case)
    case App(exp, arg) => {
      val mFBV = freevars_boundvars_constants_of(exp)
      val nFBV = freevars_boundvars_constants_of(arg)
      ((mFBV._1 ::: nFBV._1).distinct, (mFBV._2 ::: nFBV._2).distinct, (mFBV._3 ::: nFBV._3).distinct)
    }
    case AbsInScope(v, exp) => {
      val mFBV = freevars_boundvars_constants_of(exp)
      val bound = removeDoubles(mFBV._2 ::: List(v))
      (mFBV._1, bound, mFBV._3)
    }
  }



  def isFirstOrderType( exptype: TA ) = isFunctionType( exptype ) || isPredicateType( exptype )

  def isFunctionType( exptype: TA ) = checkType( exptype, Ti(), Ti() )

  def isPredicateType( exptype: TA ) = checkType( exptype, To(), Ti() )

  def checkType( toCheck: TA, retType : TA, argType: TA ) : Boolean =
    toCheck match {
      case t : Ti => t == retType
      case t : To => t == retType
      case ->(ta, tr) => ta == argType && checkType( tr, retType, argType )
  }

  def replaceLeftmostBoundOccurenceOf(variable : FOLVar, by : FOLVar, formula : FOLFormula) :
   (Boolean, FOLFormula) = {
    //println("replacing "+variable+" by "+by+" in "+formula)
    formula match {
      case Atom(_, _) => (false, formula)

      case Neg(f) =>
        val r = replaceLeftmostBoundOccurenceOf(variable, by, f )
        (r._1, Neg(r._2))

      case And(f1,f2) =>
        val r1 = replaceLeftmostBoundOccurenceOf(variable, by, f1)
        if (r1._1 == true)
          (true, And(r1._2, f2))
        else {
          val r2 = replaceLeftmostBoundOccurenceOf(variable, by, f2)
          (r2._1, And(f1, r2._2))
        }

      case Or(f1,f2) =>
        val r1 = replaceLeftmostBoundOccurenceOf(variable, by, f1)
        if (r1._1 == true)
          (true, Or(r1._2, f2))
        else {
          val r2 = replaceLeftmostBoundOccurenceOf(variable, by, f2)
          (r2._1, Or(f1, r2._2))
        }

      case ExVar(v, f)  =>
          val r = replaceLeftmostBoundOccurenceOf(variable, by, f)
          (r._1, ExVar(v, r._2))

      case AllVar(v, f)  =>
        if ((v =^ variable) && (v != variable)) {
          println("Warning: comparing two variables, which have the same sytactic representatio but differ on other things (probably different binding context)")
        }

        if (v == variable) {
          (true, AllVar(by, Substitution[LambdaExpression](variable, by).apply(f).asInstanceOf[FOLFormula]))
        }
        else {
          val r = replaceLeftmostBoundOccurenceOf(variable, by, f)
          (r._1, AllVar(v, r._2))
        }

       case _ => throw new Exception("Unknown operator encountered during renaming of outermost bound variable. Formula is: "+formula)

    }
  }


  def replaceFreeOccurenceOf(variable : FOLVar, by : FOLVar, formula : FOLFormula) : FOLFormula = {
    formula match {
      case Atom(_, args) => Substitution[LambdaExpression](variable, by).apply(formula).asInstanceOf[FOLFormula]

      case Neg(f) =>
        Neg(replaceFreeOccurenceOf(variable, by, f ))

      case And(f1,f2) =>
        val r1 = replaceFreeOccurenceOf(variable, by, f1)
        val r2 = replaceFreeOccurenceOf(variable, by, f2)
        And(r1,r2)

      case Or(f1,f2) =>
        val r1 = replaceFreeOccurenceOf(variable, by, f1)
        val r2 = replaceFreeOccurenceOf(variable, by, f2)
        Or(r1,r2)

      case ExVar(v, f)  =>
        if (v.syntaxEquals(variable))
          formula
        else
          ExVar(v, replaceFreeOccurenceOf(variable, by, f))

      case AllVar(v, f)  =>
        if (v.syntaxEquals(variable))
          formula
        else
          AllVar(v, replaceFreeOccurenceOf(variable, by, f))

       case _ => throw new Exception("Unknown operator encountered during renaming of outermost bound variable. Formula is: "+formula)

    }
  }

  def removeDoubles[T](l : List[T]) : List[T] = {
    removeDoubles_(l.reverse).reverse
  }

  private def removeDoubles_[T](l : List[T]) : List[T] = {
    l match {
      case head :: tail =>
        if (tail.contains(head))
          removeDoubles(tail)
        else
          head :: removeDoubles(tail)
      case Nil => Nil
    }
  }

  def between(lower :Int, upper : Int) : List[Int] = {
    if (lower > upper)
      List()
    else
      lower :: between (lower+1, upper)
  }
}