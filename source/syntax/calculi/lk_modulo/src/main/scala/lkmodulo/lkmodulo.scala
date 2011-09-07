package at.logic.calculi.lkmodulo

import _root_.at.logic.calculi.proofs.UnaryRuleTypeA
import _root_.at.logic.language.fol._
import _root_.at.logic.language.fol.equations.Equation
import _root_.at.logic.language.hol.logicSymbols.{ConstantStringSymbol, ConstantSymbolA}
import _root_.at.logic.language.hol.{Formula, HOLFormula, HOLExpression}
import _root_.at.logic.language.lambda.substitutions.Substitution
import _root_.at.logic.language.lambda.symbols.{SymbolA, VariableSymbolA, VariableStringSymbol}
import _root_.at.logic.language.lambda.typedLambdaCalculus._
import _root_.at.logic.language.lambda.types.{To, Ti, TA, ->}
import at.logic.calculi.lk.base.LKProof
import at.logic.calculi.lk._
import collection.immutable.{HashMap, HashSet}
import collection.mutable.StringBuilder
import math.Ordering.String

trait LKModuloRule

case object ConversionLeftRuleType extends UnaryRuleTypeA
case object ConversionRightRuleType extends UnaryRuleTypeA


abstract class REequalityA {
  val equational_rules : Set[Equation];
  val rewrite_rules : Set[Tuple2[FOLFormula, FOLFormula]];

  def reequal_to(s : FOLFormula, t : FOLFormula) : Boolean;
}

object FOLUtils {
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
      (removeDoubles(mFBV._1 ::: nFBV._1), removeDoubles(mFBV._2 ::: nFBV._2), removeDoubles(mFBV._3 ::: nFBV._3))
    }
    case AbsInScope(v, exp) => {
      val mFBV = freevars_boundvars_constants_of(exp)
      val bound = removeDoubles(mFBV._2 ::: List(v))
      (mFBV._1, bound, mFBV._3)
    }
  }

  def isfunctiontype(exptype : TA) : Boolean = {
    exptype match {
      case Ti() => true
      case To() => false
      case Ti() -> t2 => (isfunctiontype(t2))
      case _ => false
    }
  }

  def ispredicatetype(exptype : TA) : Boolean = {
    exptype match {
      case Ti() => false
      case To() => true
      case Ti() -> t2 => (ispredicatetype(t2))
      case _ => false
    }
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


/*  def replaceFreeOccurenceOf(variable : FOLVar, by : FOLVar, formula : FOLFormula) : FOLFormula = {
    val s = Substitution[FOLExpression](variable, by)
    val r = s(formula)

  }*/

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

class TPTP(val axioms : Seq[FOLFormula], val conjectures : Seq[FOLFormula]) {

  override def toString() = {
    val builder = new StringBuilder()

    var count = 0
    for (formula <- axioms) {
      builder append ("fof(axiom")
      builder append (count)
      builder append (", axiom, ")
      builder append (Renaming.fol_as_tptp(formula) )
      builder append (").\n\n")

      count = count + 1
    }

    for (formula <- conjectures) {
      builder append ("fof(formula")
      builder append (count)
      builder append (", conjecture, ")
      builder append (Renaming.fol_as_tptp(formula) )
      builder append (").\n\n")

      count = count + 1
    }
    builder.toString()
  }

}

object TPTP {
  def apply(conjectures: Seq[FOLFormula]) = new TPTP(Nil, conjectures)
  def apply(axioms : Seq[FOLFormula], conjectures: Seq[FOLFormula]) = new TPTP(axioms, conjectures)
}

object Renaming {
  import at.logic.calculi.lkmodulo.FOLUtils._


  def fol_as_tptp(f: FOLFormula) = fol_as_tptp_(tptp_renaming_of(f).asInstanceOf[FOLFormula])

  private def fol_as_tptp_(f: FOLFormula) : String = {
    f match {
      case Atom(_,_) => f.toString()
      case Neg(f1) => "~(" + fol_as_tptp_(f1) +")"
      case And(f1,f2) => "(" + fol_as_tptp_(f1) + ") & (" + fol_as_tptp_(f2) +")"
      case Or(f1,f2)  => "(" + fol_as_tptp_(f1) + ") | (" + fol_as_tptp_(f2) +")"
      case Imp(f1,f2) => "(" + fol_as_tptp_(f1) + ") => (" + fol_as_tptp_(f2) + ")"
      case ExVar(v,f1)  => "?[" + v + "] : (" + fol_as_tptp_(f1) +")"
      case AllVar(v,f1) => "![" + v + "] : (" + fol_as_tptp_(f1) +")"
      case _ => println("unhandled case!"); "(???)"
    }
  }


  def createAlphanormalizationSymbol(v : Var, n : Int) = {
    if (v.name.isInstanceOf[ConstantSymbolA]) {
      //constants
      if (ispredicatetype(v.exptype))
        new ConstantStringSymbol("P_"+n)
      else if (isfunctiontype(v.exptype))
        new ConstantStringSymbol("f_"+n)
      else new ConstantStringSymbol("s_"+n)
    } else {
      //everything else => variables
      if (ispredicatetype(v.exptype))
        new VariableStringSymbol("X_"+n)
      else if (isfunctiontype(v.exptype))
        new VariableStringSymbol("x_"+n)
      else
        new VariableStringSymbol("t_"+n)
    }
  }

  def createTPTPExportSymbol(v : Var, n : Int) = {
    if (v.name.isInstanceOf[ConstantSymbolA]) {
      //constants
      if (ispredicatetype(v.exptype))
        //new ConstantStringSymbol("p_"+n)
        new ConstantStringSymbol("p_" + v.name)
      else if (isfunctiontype(v.exptype))
//        new ConstantStringSymbol("f_"+n)
        new ConstantStringSymbol("f_" + v.name)
      else
        throw new Exception("in fol, we can only rename if a symbol is of function or predicate type")
    } else {
      //everything else => variables
      if (ispredicatetype(v.exptype))
        throw new Exception("in fol, we should not have predicate variables")
      else if (isfunctiontype(v.exptype))
        new VariableStringSymbol("X_"+n)
      else
        throw new Exception("in fol, we can only rename if a symbol is of function or predicate type")
    }
  }

  def define_normalization_function(normalization_fun : ((Var, Int) => SymbolA), f : LambdaExpression) = {
    val freeandbound = freevars_boundvars_constants_of(f)

    val allvars = freeandbound._1 ++ freeandbound._2 ++ freeandbound._3.filter((v:Var) => ispredicatetype(v.exptype) || isfunctiontype(v.exptype) )
    //TODO: this is only applicable to variablestringsymbol and constantstringsymbol


    var count = 0
    val assignednames : List[Var] = allvars map ((v:Var) => { count=count+1; v.factory.createVar(normalization_fun(v, count), v.exptype) })
    val map  = HashMap() ++ (allvars zip assignednames)
//    println("formula: "+ f+ " map: " + map)

    val fun = (v:Var) => if (! map.contains(v)) { /* println("warning: ecnountered "+v+" which is not in the map!"); */ v } else map(v)
    fun
  }


  def canonical_renaming_of(f: LambdaExpression) : LambdaExpression = {
    replaceAll(define_normalization_function(createAlphanormalizationSymbol, f), f)
  }

  def tptp_renaming_of(f: LambdaExpression) : LambdaExpression = {
    replaceAll(define_normalization_function(createTPTPExportSymbol, f), f)
  }


  private def replaceAll(exchange : (Var => Var), f : LambdaExpression) : LambdaExpression = {
    f match {
      case v : Var =>
        exchange(v)
      case App(fun, arg) =>
        fun.factory.createApp(replaceAll(exchange,fun), replaceAll(exchange, arg))
      case AbsInScope(lambdavar, exp) =>
        //println("replacing "+lambdavar+" by "+exchange(lambdavar))
        lambdavar.factory.createAbs(exchange(lambdavar), replaceAll(exchange, exp))
      //case Abs(lambdavar, exp) =>
      //    lambdavar.factory.createAbs(exchange(lambdavar), replaceAll(exchange, exp))

      case _ => throw new Exception("replaceAll encountered something else than Var, App, Abs (InScope) during deconstruction of a lambda expression")
    }

  }




  def canonical_renaming_of(f: FOLFormula) : FOLFormula = {
    val boundandfree = freevars_boundvars_constants_of(f)
    val free_variables : List[Var] = boundandfree._1.toList
    val bound_variables : List[Var] = boundandfree._2.toList.map(
      (x : Var) => x match { case Var(symbol, exptype) =>  (x.factory.createVar(symbol,exptype)) }
    )

    var freevar_count = free_variables.size
    val names : List[FOLVar] = between(0, freevar_count - 1).map((n:Int) => FOLVar(new VariableStringSymbol("x_" + n) ))

    //println(boundandfree)

    var sentence = f
    for (pair <- free_variables zip names) {
      sentence = replaceFreeOccurenceOf(pair._1.asInstanceOf[FOLVar], pair._2, sentence)
    }

    for (v <- bound_variables) {
      sentence = replaceLeftmostBoundOccurenceOf(v.asInstanceOf[FOLVar], FOLVar(new VariableStringSymbol("x_"+freevar_count)), sentence)._2
      freevar_count = freevar_count +1
    }

    //println(sentence)

    sentence
  }

   private def canonical_renaming_of(f: FOLFormula, index : Int) : (FOLFormula, Int) = {
     (f,index)
   }

}


abstract class EequalityA extends REequalityA {
  /* the set of rewrite rules is empty in a pure equational theory */
  override val rewrite_rules = Set[Tuple2[FOLFormula, FOLFormula]]()
  override def reequal_to(s : FOLFormula, t : FOLFormula) : Boolean = reequal_to_(s,t)



  private def reequal_to_(s : FOLFormula, t : FOLFormula) : Boolean = {
    def tuples_equals(el : Tuple2[FOLTerm, FOLTerm] ) : Boolean = (word_equalsto(el._1, el._2))

    (s,t) match {
      case (Atom( sym1: ConstantSymbolA, args1: List[FOLTerm]), Atom( sym2: ConstantSymbolA, args2: List[FOLTerm])) =>
        (sym1 == sym2) &&
        (args1.length == args2.length) &&
        ( (args1 zip args2) forall (tuples_equals))

      case (Neg(f1), Neg(f2)) =>
        reequal_to_(f1,f2)

      case (And(f1,f2), And(g1,g2)) =>
        reequal_to_(f1,g2) && reequal_to (f2,g2)

      case (Or(f1,f2), Or(g1,g2)) =>
        reequal_to_(f1,g2) && reequal_to (f2,g2)

      /* these two rules work only if the variables are canonically renamed in both formulas */
      case (AllVar(x1,t1), AllVar(x2,t2)) =>
        (x1 == x2) && reequal_to_ (t1,t2)

      case (ExVar(x1,t1), ExVar(x2,t2)) =>
        (x1 == x2) && reequal_to_ (t1,t2)

      case default => false
    }
  }

  def word_equalsto(s : FOLTerm, t : FOLTerm) : Boolean
  def unifies_with(s : FOLTerm, t : FOLTerm) : Option[Substitution[FOLTerm]]
}


object ConversionRightRule {
  def apply(premise : LKProof ) = null
}