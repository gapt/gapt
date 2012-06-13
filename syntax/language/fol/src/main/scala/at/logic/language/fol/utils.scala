/**
 * Created by IntelliJ IDEA.
 * User: marty
 * Date: 10/3/11
 * Time: 5:16 PM
 */

package at.logic.language.fol

import _root_.at.logic.language.hol.logicSymbols.ConstantSymbolA
import _root_.at.logic.language.lambda.substitutions.Substitution
import _root_.at.logic.language.lambda.symbols.VariableSymbolA
import _root_.at.logic.language.lambda.typedLambdaCalculus.{AbsInScope, App, Var, LambdaExpression}
import _root_.at.logic.language.lambda.types.->
import _root_.at.logic.language.lambda.types.{To, Ti, TA}

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
