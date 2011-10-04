package at.logic.calculi.lkmodulo

import _root_.at.logic.calculi.lkmodulo.Equation
import _root_.at.logic.calculi.proofs.UnaryRuleTypeA
import _root_.at.logic.language.fol.{Function, FOLConst, Imp, Atom, Neg, And, Or, ExVar, AllVar, FOLVar, getFreeVariablesFOL, FOLTerm, FOLFormula, Equation => FOLEquation}
import _root_.at.logic.language.hol.logicSymbols.{ConstantStringSymbol, ConstantSymbolA}
import _root_.at.logic.language.hol.{Formula, HOLFormula, HOLExpression}
import _root_.at.logic.language.lambda.substitutions.Substitution
import _root_.at.logic.language.lambda.symbols.{SymbolA, VariableSymbolA, VariableStringSymbol}
import _root_.at.logic.language.lambda.typedLambdaCalculus._
import _root_.at.logic.language.lambda.types.{To, Ti, TA, ->}
import _root_.at.logic.parsing.readers.StringReader
import at.logic.calculi.lk.base.LKProof
import at.logic.calculi.lk._
import collection.immutable.{HashMap, HashSet}
import collection.mutable.StringBuilder
import math.Ordering.String
import at.logic.parsing.language.simple.SimpleFOLParser
import types.Equation

trait LKModuloRule

case object ConversionLeftRuleType extends UnaryRuleTypeA
case object ConversionRightRuleType extends UnaryRuleTypeA


package types {
class Equation(val left: FOLTerm, val right : FOLTerm) {
  def toFormula() = FOLEquation(left, right)
}
}

object Equation {
  def apply(left : FOLTerm , right : FOLTerm ) = new Equation(left,  right)

  /*
  def unapply(f : FOLFormula) = {
    f match {
      case FOLEquation(left, right) => Some(Equation(left, right))
      case _ => None
    }
  }*/

  implicit def equation2formula(e : Equation) = e.toFormula()
}

abstract class REequalityA {
  def equational_rules() : Set[Equation];
  def rewrite_rules() : Set[Tuple2[FOLFormula, FOLFormula]];

  def reequal_to(s : FOLFormula, t : FOLFormula) : Boolean;
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
  import at.logic.language.fol.Utils._


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
      if (isPredicateType(v.exptype))
        new ConstantStringSymbol("P_"+n)
      else if (isFunctionType(v.exptype))
        new ConstantStringSymbol("f_"+n)
      else new ConstantStringSymbol("s_"+n)
    } else {
      //everything else => variables
      if (isPredicateType(v.exptype))
        new VariableStringSymbol("X_"+n)
      else if (isFunctionType(v.exptype))
        new VariableStringSymbol("x_"+n)
      else
        new VariableStringSymbol("t_"+n)
    }
  }

  def createTPTPExportSymbol(v : Var, n : Int) = {
    if (v.name.isInstanceOf[ConstantSymbolA]) {
      //constants
      if (isPredicateType(v.exptype))
        //new ConstantStringSymbol("p_"+n)
        new ConstantStringSymbol("p_" + v.name)
      else if (isFunctionType(v.exptype))
//        new ConstantStringSymbol("f_"+n)
        new ConstantStringSymbol("f_" + v.name)
      else
        throw new Exception("in fol, we can only rename if a symbol is of function or predicate type")
    } else {
      //everything else => variables
      if (isPredicateType(v.exptype))
        throw new Exception("in fol, we should not have predicate variables")
      else if (isFunctionType(v.exptype))
        new VariableStringSymbol("X_"+n)
      else
        throw new Exception("in fol, we can only rename if a symbol is of function or predicate type")
    }
  }

  def define_normalization_function(normalization_fun : ((Var, Int) => SymbolA), f : LambdaExpression) = {
    val freeandbound = freevars_boundvars_constants_of(f)

    val allvars = freeandbound._1 ++ freeandbound._2 ++ freeandbound._3.filter((v:Var) => isFirstOrderType(v.exptype) )
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
  final override def rewrite_rules() = Set[Tuple2[FOLFormula, FOLFormula]]()
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