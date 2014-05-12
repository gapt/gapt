/*
 * FOLerization.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.fol

import at.logic.language.fol._
import at.logic.language.hol.{HOLExpression, HOLVar, HOLConst, Neg => HOLNeg, And => HOLAnd, Or => HOLOr, Imp => HOLImp, Function => HOLFunction, Atom => HOLAtom, HOLFormula}
import at.logic.language.hol.{ExVar => HOLExVar, AllVar => HOLAllVar}
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types._
import at.logic.language.lambda.symbols._
import scala.collection.mutable
import at.logic.calculi.lk.base.types._
import at.logic.language.hol.{HOLApp, HOLAbs, Function => HOLFunction}
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.schema.{IntZero,Succ,foVar, foConst,IntegerTerm,indexedFOVar}

package hol2fol {

import at.logic.language.hol.HOLOrdering
import at.logic.calculi.lk.base.FSequent
import at.logic.calculi.lk.base.types.FSequent
import at.logic.language.lambda.substitutions.Substitution


/**
 * Try to reduce high order terms to first order terms by changing the types if possible. Closed lambda expression are
 * replaced by constants. Open lambda expressions are changed by functions.
 */
object reduceHolToFol extends reduceHolToFol
class reduceHolToFol {
  private def folexp2term(exp:FOLExpression) = exp match {
    case e:FOLTerm => exp.asInstanceOf[FOLTerm]
    case _ => throw new Exception("Cannot cast "+exp+" to a fol term!"+exp.getClass)
  }

  //TODO: replace mutable maps by immutable ones to allow parallelism. Need to check the calls for sideffects on the maps
  def apply(formula: HOLFormula, scope: mutable.Map[LambdaExpression, ConstantStringSymbol], id: {def nextId: Int}): FOLFormula = {
    val immscope = Map[LambdaExpression, ConstantStringSymbol]() ++ scope
    val (scope_, qterm) = replaceAbstractions(formula, immscope, id)
    scope ++= scope_
    apply_( qterm).asInstanceOf[FOLFormula]
  }

  // convienience method creating empty scope and default id
  def apply(term: HOLExpression) : FOLExpression = {
    val counter = new {private var state = 0; def nextId = { state = state +1; state}}
    val emptymap = mutable.Map[LambdaExpression, ConstantStringSymbol]()
    reduceHolToFol( term, emptymap, counter )
  }

  def apply(formula: HOLFormula) : FOLFormula =
  //inner cast needed to call the correct apply method
    reduceHolToFol(formula.asInstanceOf[HOLExpression]).asInstanceOf[FOLFormula]

  def apply(term: HOLExpression, scope: mutable.Map[LambdaExpression, ConstantStringSymbol], id: {def nextId: Int}) = {
    val immscope = Map[LambdaExpression, ConstantStringSymbol]() ++ scope
    val (scope_, qterm) = replaceAbstractions(term, immscope, id)
    scope ++= scope_
    apply_( qterm)
  }

  def apply(s: FSequent, scope: mutable.Map[LambdaExpression, ConstantStringSymbol], id: {def nextId: Int}): FSequent = {
    val immscope = Map[LambdaExpression,ConstantStringSymbol]() ++ scope
    val (scope1, ant) = s.antecedent.foldLeft((immscope, List[HOLFormula]()))((r, formula) => {
      val (scope_, f_) = replaceAbstractions(formula, r._1, id)
      (scope_, f_.asInstanceOf[HOLFormula] :: r._2)
    })
    val (scope2, succ) = s.succedent.foldLeft((scope1, List[HOLFormula]()))((r, formula) => {
      val (scope_, f_) = replaceAbstractions(formula, r._1, id)
      (scope_, f_.asInstanceOf[HOLFormula] :: r._2)
    })
    scope ++= scope2
    FSequent( ant map apply_, succ map apply_  )
  }

  def apply_(f:HOLFormula) : FOLFormula =
    apply_(f.asInstanceOf[HOLExpression]).asInstanceOf[FOLFormula]

  //assumes we are on the logical level of the hol formula - all types are mapped to i, i>o or i>i>o respectively
  def apply_(term: HOLExpression): FOLExpression = {
    term match {
      case e : FOLExpression => e // if it's already FOL - great, we are done.
      case z:indexedFOVar => FOLVar(new VariableStringSymbol(z.name.toString ++ intTermLength(z.index.asInstanceOf[IntegerTerm]).toString))
      case fov: foVar => FOLVar(new VariableStringSymbol(fov.name.toString))
      case foc: foConst => FOLConst(new ConstantStringSymbol(foc.name.toString))
      case HOLVar(n, _) => FOLVar(n)
      case HOLConst(n, _) => FOLConst(n)
      case HOLNeg(n) => Neg(apply_(n))
      case HOLAnd(n1,n2) => And(apply_(n1), apply_(n2))
      case HOLOr(n1,n2) => Or(apply_(n1), apply_(n2))
      case HOLImp(n1,n2) => Imp(apply_(n1), apply_(n2))
      case HOLAllVar(v: HOLVar,n) => AllVar(apply_(v).asInstanceOf[FOLVar], apply_(n))
      case HOLExVar(v: HOLVar,n) => ExVar(apply_(v).asInstanceOf[FOLVar], apply_(n))
      case HOLAtom(n, ls) =>
        Atom(ConstantStringSymbol(n.toString()), ls.map(x => folexp2term(apply_termlevel(x))))
      case HOLFunction(n, ls, _) =>
        Function(ConstantStringSymbol(n.toString), ls.map(x => folexp2term(apply_(x))))

      //this case is added for schema
      case HOLApp(func,arg) => {
        func match {
          case HOLVar(sym,_) => {
            val new_arg = apply_(arg).asInstanceOf[FOLTerm]
            return at.logic.language.fol.Function(new ConstantStringSymbol(sym.toString), new_arg::Nil)
          }
          case _ => println("\nWARNING: FO schema term!\n")
        }
        throw new Exception("\nProbably unrecognized object from schema!\n")
      }
      case _ => throw new IllegalArgumentException("Cannot reduce hol term: " + term.toString + " to fol as it is a higher order variable function or atom") // for cases of higher order atoms and functions
    }
  }

  //if we encountered an atom, we need to convert logical formulas to the term level too
  def apply_termlevel(term: HOLExpression): FOLTerm = {
    term match {
      case e : FOLTerm => e // if it's already FOL - great, we are done.
      case z:indexedFOVar => FOLVar(new VariableStringSymbol(z.name.toString ++ intTermLength(z.index.asInstanceOf[IntegerTerm]).toString))
      case fov: foVar => FOLVar(new VariableStringSymbol(fov.name.toString))
      case foc: foConst => FOLConst(new ConstantStringSymbol(foc.name.toString))
      case HOLVar(n, _) => FOLVar(n)
      case HOLConst(n, _) => FOLConst(n)
      case HOLNeg(n) => Function(NegSymbol,  List(apply_termlevel(n)))
      case HOLAnd(n1,n2) => Function(AndSymbol, List(apply_termlevel(n1), apply_termlevel(n2)))
      case HOLOr(n1,n2) => Function(OrSymbol, List(apply_termlevel(n1), apply_termlevel(n2)))
      case HOLImp(n1,n2) => Function(ImpSymbol, List(apply_termlevel(n1), apply_termlevel(n2)))
      case HOLAllVar(v: HOLVar,n) =>
        Function(ForallSymbol, List(apply_termlevel(v).asInstanceOf[FOLVar], apply_termlevel(n)))
      case HOLExVar(v: HOLVar,n) =>
        Function(ExistsSymbol, List(apply_termlevel(v).asInstanceOf[FOLVar], apply_termlevel(n)))
      case HOLAtom(n: SymbolA, ls) =>
        Function(ConstantStringSymbol(n.toString()), ls.map(x => folexp2term(apply_termlevel(x))))
      case HOLFunction(n: ConstantSymbolA, ls, _) => Function(n, ls.map(x => folexp2term(apply_termlevel(x))))

      //this case is added for schema
      case HOLApp(func,arg) => {
        func match {
          case HOLVar(sym,_) => {
            val new_arg = apply_(arg).asInstanceOf[FOLTerm]
            return at.logic.language.fol.Function(new ConstantStringSymbol(sym.toString), new_arg::Nil)
          }
          case _ => println("\nWARNING: FO schema term!\n")
        }
        throw new Exception("\nProbably unrecognized object from schema!\n")
      }
      case _ => throw new IllegalArgumentException("Cannot reduce hol term: " + term.toString + " to fol as it is a higher order variable function or atom") // for cases of higher order atoms and functions
    }
  }



  //transforms a ground integer term to Int
  private def intTermLength(t: IntegerTerm): Int = t match {
    case c: IntZero => 0
    case Succ(t1) => 1 + intTermLength(t1)
    case _ => throw new Exception("\nError in reduceHolToFol.length(...) !\n")
  }
}


object replaceAbstractions extends replaceAbstractions
class replaceAbstractions {
  type ConstantsMap = Map[LambdaExpression,ConstantStringSymbol]

  def apply(l : List[FSequent]) : (ConstantsMap, List[FSequent]) = {
    val counter = new {private var state = 0; def nextId = { state = state +1; state}}
    val emptymap = Map[LambdaExpression, ConstantStringSymbol]()
    l.foldLeft((emptymap,List[FSequent]()))( (rec,el) => {
      val (scope_,f) = rec
      val (nscope, rfs) = replaceAbstractions(el, scope_,counter)
      (nscope, rfs::f)

    })
  }

  def apply(f:FSequent, scope : ConstantsMap, id: {def nextId: Int}) : (ConstantsMap,FSequent) = {
    val (scope1, ant) = f.antecedent.foldLeft((scope,List[HOLFormula]()))((rec,formula) => {
      val (scope_, f) = rec
      val (nscope, nformula) = replaceAbstractions(formula, scope_, id)
      (nscope, nformula.asInstanceOf[HOLFormula]::f)
    })
    val (scope2, succ) = f.succedent.foldLeft((scope1,List[HOLFormula]()))((rec,formula) => {
      val (scope_, f) = rec
      val (nscope, nformula) = replaceAbstractions(formula, scope_, id)
      (nscope, nformula.asInstanceOf[HOLFormula]::f)
    })

    (scope2, FSequent(ant.reverse, succ.reverse))
  }

  // scope and id are used to give the same names for new functions and constants between different calls of this method
  def apply(e : HOLExpression, scope : ConstantsMap, id: {def nextId: Int})
  : (ConstantsMap, HOLExpression) = e match {
    case HOLVar(_,_) =>
      (scope,e)
    case HOLConst(_,_) =>
      (scope,e)
    case HOLApp(s,t) =>
      val (scope1,s1) = replaceAbstractions(s, scope, id)
      val (scope2,t1) = replaceAbstractions(t, scope1, id)
      (scope2, HOLApp(s1,t1))
    //quantifiers should be kept
    case HOLAllVar(x,f) =>
      val (scope_, e_) = replaceAbstractions(f,scope,id)
      (scope_, HOLAllVar(x,e_.asInstanceOf[HOLFormula]))
    case HOLExVar(x,f) =>
      val (scope_, e_) = replaceAbstractions(f,scope,id)
      (scope_, HOLExVar(x,e_.asInstanceOf[HOLFormula]))
    // This case replaces an abstraction by a function term.
    // the scope we choose for the variant is the Abs itself as we want all abs identical up to variant use the same symbol
    case HOLAbs(v, exp) =>
      //systematically rename free variables for the index
      val normalizeda = e.variant(new VariantGenerator(new {var idd = 0; def nextId = {idd = idd+1; idd}}, "myVariantName"))
      //println("e: "+e)
      //println("norm: "+normalizeda)
      //update scope with a new constant if neccessary
      //println(scope)
      val scope_ = if (scope contains normalizeda) scope else scope + ((normalizeda,ConstantStringSymbol("q_{" + id.nextId + "}")))
      //println(scope_)
      val sym = scope_(normalizeda)

      val freeVarList = e.getFreeVariables.toList.sortBy(_.toString).asInstanceOf[List[HOLExpression]]
      if (freeVarList.isEmpty)
        (scope_, HOLConst( sym, e.exptype ))
      else
        (scope_, HOLFunction(sym, freeVarList, e.exptype))
    case _ =>
      throw new Exception("Unhandled case in abstraction replacement!"+e)

  }
}

/**
 * In contrast to reduceHolToFol, we recreate the term via the fol constructors but
 * do not try to remove higher-order content.
 */
object convertHolToFol extends convertHolToFol
class convertHolToFol {
  def apply(e:LambdaExpression) : FOLFormula = convertFormula(e)
  def apply(e:HOLFormula) : FOLFormula = convertFormula(e)
  def apply(fs:FSequent) : FSequent =
    FSequent(fs.antecedent.map(apply), fs.succedent.map(apply))

  def convertFormula(e:LambdaExpression) : FOLFormula = e match {
    case HOLAtom(sym:ConstantSymbolA, args)
      if (args.filterNot(_.exptype == Ti()).isEmpty) =>
      Atom(sym, args map convertTerm)

    case HOLNeg(x) => Neg(convertFormula(x))
    case HOLAnd(x,y) => And(convertFormula(x),convertFormula(y))
    case HOLOr(x,y) => Or(convertFormula(x),convertFormula(y))
    case HOLImp(x,y) => Imp(convertFormula(x),convertFormula(y))
    case HOLAllVar(x@Var(_, Ti()), t) => AllVar(convertTerm(x).asInstanceOf[FOLVar],convertFormula(t))
    case HOLExVar(x@Var(_, Ti()), t) => ExVar(convertTerm(x).asInstanceOf[FOLVar],convertFormula(t))
    case _ => throw new Exception("Could not convert term "+e+" to first order!")
  }

  def convertTerm(e:LambdaExpression) : FOLTerm = e match {
    case HOLVar(x:VariableSymbolA, Ti()) => FOLVar(x)
    case HOLConst(x:ConstantSymbolA, Ti()) => FOLConst(x)
    case HOLFunction(f:ConstantSymbolA, args, Ti())
      if (args.filterNot(_.exptype == Ti()).isEmpty) =>
      Function(f, args map convertTerm)
    case _ => throw new Exception("Could not convert term "+e+" to first order!")
  }

}

// TODO - support generated function symbols by checking the arity from le and add the variables to the returned term. Right now only constants are supported
object createExampleFOLConstant {
  def apply(le: LambdaExpression, css: ConstantStringSymbol) = FOLConst(css)
}

/**
 * Introducing abstractions and converting to fol changes more complex types to fol compatible ones. With changeTypeIn
 * you can change them back.
 */
object changeTypeIn {
  type TypeMap = Map[String, TA]

  /* TODO: this broken, since e.g. for (a b) q with type(q)=alpha, type(b)=beta then type(a)=beta > (alpha > gamma)
     we need to actually change the type of a when changing the type of q
    */
  def oldapply(e:LambdaExpression, tmap : TypeMap) : LambdaExpression = e match {
    case Var(name, ta) =>
      if (tmap.contains(name.toString()))
        e.factory.createVar(name, tmap(name.toString()))
      else
        e
    case App(s,t) => s.factory.createApp(oldapply(s,tmap), oldapply(t,tmap))
    case Abs(x,t) => t.factory.createAbs(oldapply(x,tmap).asInstanceOf[Var], oldapply(t,tmap))
  }

  //Remark: this only works for changing the type of leaves in the term tree!
  def apply(e:HOLExpression, tmap : TypeMap) : HOLExpression = e match {
    case HOLVar(name, ta) => if (tmap contains name.toString()) HOLVar(name, tmap(name.toString())) else
                                                                HOLVar(name,ta)
    case HOLConst(name, ta) => if (tmap contains name.toString()) HOLConst(name, tmap(name.toString())) else
                                                                  HOLConst(name,ta)
    case HOLFunction(f, args, rv) => HOLFunction(f, args.map(x => apply(x,tmap)), rv)
    case HOLAtom(f, args) => HOLAtom(f, args.map(x => apply(x,tmap)))
    case HOLNeg(x) => HOLNeg(apply(x,tmap))
    case HOLAnd(s,t) => HOLAnd(apply(s,tmap), apply(t,tmap))
    case HOLOr(s,t) => HOLOr(apply(s,tmap), apply(t,tmap))
    case HOLImp(s,t) => HOLImp(apply(s,tmap), apply(t,tmap))
    case HOLAllVar(x,t) => HOLAllVar(apply(x.asInstanceOf[HOLVar],tmap).asInstanceOf[HOLVar], apply(t,tmap))
    case HOLExVar(x,t) => HOLExVar(apply(x.asInstanceOf[HOLVar],tmap).asInstanceOf[HOLVar], apply(t,tmap))
    case HOLAbs(x,t) => HOLAbs(apply(x.asInstanceOf[HOLVar],tmap).asInstanceOf[HOLVar], apply(t,tmap))
    case HOLApp(s,t) => HOLApp(apply(s,tmap), apply(t,tmap))
    case _ => throw new Exception("Unhandled case of a HOL Formula! "+e)

  }
  def apply(e:FOLExpression, tmap : TypeMap) : FOLExpression = apply(e.asInstanceOf[HOLExpression], tmap).asInstanceOf[FOLExpression]
  def apply(e:HOLFormula, tmap : TypeMap) : HOLFormula = apply(e.asInstanceOf[HOLExpression], tmap).asInstanceOf[HOLFormula]
  def apply(e:FOLFormula, tmap : TypeMap) : FOLFormula = apply(e.asInstanceOf[HOLExpression], tmap).asInstanceOf[FOLFormula]
  def apply(fs:FSequent, tmap:TypeMap) : FSequent = FSequent(fs.antecedent.map(x=> apply(x,tmap)),
                                                             fs.succedent.map(x=> apply(x,tmap)) )

  //different names bc of type erasure
  def holsub(s:Substitution[HOLExpression], tmap : TypeMap) : Substitution[HOLExpression] = Substitution[HOLExpression](s.map.map(x =>
    (apply(x._1.asInstanceOf[HOLVar], tmap).asInstanceOf[Var], apply(x._2, tmap) )
  ))

  def folsub(s:Substitution[FOLExpression], tmap : TypeMap) : Substitution[FOLExpression] = Substitution[FOLExpression](s.map.map(x =>
    (apply(x._1.asInstanceOf[HOLVar], tmap).asInstanceOf[Var], apply(x._2, tmap) )
  ))
}



}
