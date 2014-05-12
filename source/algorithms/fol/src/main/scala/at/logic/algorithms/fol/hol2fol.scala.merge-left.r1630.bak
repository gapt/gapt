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

package hol2fol {

import at.logic.language.hol.HOLApp
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.language.hol.logicSymbols.ConstantStringSymbol
import at.logic.language.schema.{IntZero,Succ,foVar, foConst,IntegerTerm,indexedFOVar}

/* Try to reduce high order terms to first order terms by changing the types if possible. Closed lambda expression are
 *replaced by constants. Open lambda expressions are changed by functions.
 */
  object reduceHolToFol {
    //transforms a ground integer term to Int
    private def intTermLength(t: IntegerTerm): Int = t match {
      case c: IntZero => 0
      case Succ(t1) => 1 + intTermLength(t1)
      case _ => throw new Exception("\nError in reduceHolToFol.length(...) !\n")
    }

    // scope and id are used to give the same names for new functions and constants between different calls of this method
    def apply_(term: HOLExpression, scope: mutable.Map[LambdaExpression, ConstantStringSymbol], id: {def nextId: Int}): FOLExpression = {
      term match {
        case z:indexedFOVar => FOLVar(new VariableStringSymbol(z.name.toString ++ intTermLength(z.index.asInstanceOf[IntegerTerm]).toString))
        case fov: foVar => FOLVar(new VariableStringSymbol(fov.name.toString))
        case foc: foConst => FOLConst(new ConstantStringSymbol(foc.name.toString))
        case HOLNeg(n) => Neg(reduceHolToFol(n,scope,id).asInstanceOf[FOLFormula])
        case HOLAnd(n1,n2) => And(reduceHolToFol(n1,scope,id).asInstanceOf[FOLFormula], reduceHolToFol(n2,scope,id).asInstanceOf[FOLFormula])
        case HOLOr(n1,n2) => Or(reduceHolToFol(n1,scope,id).asInstanceOf[FOLFormula], reduceHolToFol(n2,scope,id).asInstanceOf[FOLFormula])
        case HOLImp(n1,n2) => Imp(reduceHolToFol(n1,scope,id).asInstanceOf[FOLFormula], reduceHolToFol(n2,scope,id).asInstanceOf[FOLFormula])
        case HOLAllVar(v: HOLVar,n) => AllVar(reduceHolToFol(v,scope,id).asInstanceOf[FOLVar], reduceHolToFol(n,scope,id).asInstanceOf[FOLFormula])
        case HOLExVar(v: HOLVar,n) => ExVar(reduceHolToFol(v,scope,id).asInstanceOf[FOLVar], reduceHolToFol(n,scope,id).asInstanceOf[FOLFormula])
        case HOLAtom(n: ConstantSymbolA, ls) => Atom(n, ls.map(x => apply(x.asInstanceOf[HOLExpression],scope,id).asInstanceOf[FOLTerm]))
        case HOLFunction(n: ConstantSymbolA, ls, _) => Function(n, ls.map(x => apply(x.asInstanceOf[HOLExpression],scope,id).asInstanceOf[FOLTerm]))
        case HOLVar(n, _) => FOLVar(n)
        case HOLConst(n, _) => FOLConst(n)

          //this case is added for schema
        case HOLApp(func,arg) => {
          func match {
            case HOLVar(sym,_) => {
              val new_arg = apply_(arg, scope, id).asInstanceOf[FOLTerm]
              return at.logic.language.fol.Function(new ConstantStringSymbol(sym.toString), new_arg::Nil)
            }
            case _ => println("\nWARNING: FO schema term!\n")
          }
          throw new Exception("\nProbably unrecognized object from schema!\n")
        }
        // This case replaces an abstraction by a function term.
        //
        // the scope we choose for the variant is the Abs itself as we want all abs identical up to variant use the same symbol
        //
        // TODO: at the moment, syntactic equality is used here... This means that alpha-equivalent terms may be replaced
        // by different constants, which is undesirable.
        case a @ Abs(v, exp) => {
          val sym = scope.getOrElseUpdate(a.variant(new VariantGenerator(new {var idd = 0; def nextId = {idd = idd+1; idd}}, "myVariantName")), ConstantStringSymbol("q_{" + id.nextId + "}"))
          val freeVarList = a.getFreeVariables.toList.sortWith((x,y) => x.toString < y.toString).map(x => apply(x.asInstanceOf[HOLExpression],scope,id))
          if (freeVarList.isEmpty) FOLConst(sym) else Function(sym, freeVarList.asInstanceOf[List[FOLTerm]])
        }
        case _ => throw new IllegalArgumentException("Cannot reduce hol term: " + term.toString + " to fol as it is a higher order variable function or atom") // for cases of higher order atoms and functions
      }
    }

    def apply(term: HOLExpression, scope: mutable.Map[LambdaExpression, ConstantStringSymbol], id: {def nextId: Int}) =
      apply_( term, scope, id )

    def apply(formula: HOLFormula, scope: mutable.Map[LambdaExpression, ConstantStringSymbol], id: {def nextId: Int}): FOLFormula =
      apply_( formula, scope, id ).asInstanceOf[FOLFormula]

    // TODO: should return FOLSequent
    def apply(s: FSequent, scope: mutable.Map[LambdaExpression, ConstantStringSymbol], id: {def nextId: Int}): FSequent =
      new FSequent( s._1.map( f => apply(f, scope, id ) ), s._2.map( f => apply(f, scope, id ) ) )

    // convienience method creating empty scope and default id
    def apply(term: HOLExpression) : FOLExpression = {
      val counter = new {private var state = 0; def nextId = { state = state +1; state}}
      val emptymap = mutable.Map[LambdaExpression, ConstantStringSymbol]()
      reduceHolToFol( term, emptymap, counter )
    }

    def apply(formula: HOLFormula) : FOLFormula = apply(formula).asInstanceOf[FOLFormula]

  }
  // TODO - support generated function symbols by checking the arity from le and add the variables to the returned term. Right now only constants are supported
  object createExampleFOLConstant {
    def apply(le: LambdaExpression, css: ConstantStringSymbol) = FOLConst(css)
  }


}
