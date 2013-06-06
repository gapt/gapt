package at.logic.calculi.lkmodulo

import _root_.at.logic.calculi.proofs.UnaryRuleTypeA
import at.logic.language.fol.{Equation => FOLEquation, _}
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
import scala.collection.immutable
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol



/*
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

  def tptp_renaming_of(formula : FOLFormula) = {
    //rename free variables first
    val Gen = new { var counter = 0; def next() : String = {counter = counter+1; "TPTP_{"+counter+"}"} }
    val gen = new VariableNameGenerator( Gen.next )
    val vars = formula.freeVariables filterNot (_.name.toString.matches("""[A-Z][a-zA-Z0-9]*"""))
    val pairs = vars.foldLeft((formula.symbols.map(_.toString).toSet, List[(Var,FOLExpression)]()))((bl, x) => {
      val nx = gen(x,bl._1);  } )
    val sub = new Substitution[FOLExpression](  )
    val f = sub(formula).asInstanceOf[FOLFormula]
    tptp_renaming_of(f, f.symbols.map(_.toString).toSet)
  }

  def tptp_renaming_of(f : FOLFormula, blacklist : immutable.Set[String]) = {



  }




}

*/