/*
 * FOLerization.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.fol

import at.logic.language.fol._
import at.logic.language.hol.{HOLExpression, HOLVar, HOLConst, Neg => HOLNeg, And => HOLAnd, Or => HOLOr, Imp => HOLImp, Function => HOLFunction, Atom => HOLAtom}
import at.logic.language.hol.{ExVar => HOLExVar, AllVar => HOLAllVar}
import at.logic.language.hol.logicSymbols._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.types._
import at.logic.language.lambda.symbols._
import scala.collection.mutable.Map

package hol2fol {
  /* Try to reduce high order terms to first order terms by changing the types if possible. Closed lambda expression are replaced by constants. Open labda expressions are changed by functions.
   */
  object reduceHolToFol {
    // scope and id are used to give the same names for new functions and constants between different calls of this method
    def apply(term: HOLExpression, scope: Map[LambdaExpression, ConstantStringSymbol], id: {def nextId: Int}): FOLExpression = term match {
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
      // the scope we choose for the variant is the Abs itself as we want all abs identical up to variant use the same symbol
      case a @ AbsInScope(v, exp) => {
          val sym = scope.getOrElseUpdate(a.variant(new VariantGenerator(new {var idd = 0; def nextId = {idd = idd+1; idd}}, "myVariantName")), ConstantStringSymbol("q_{" + id.nextId + "}"))
          val freeVarList = exp.getFreeAndBoundVariables._1.toList.sort((x,y) => x.toString < y.toString).map(x => apply(x.asInstanceOf[HOLExpression],scope,id))
          if (freeVarList.isEmpty) FOLConst(sym) else Function(sym, freeVarList.asInstanceOf[List[FOLTerm]])
      }
      case _ => throw new IllegalArgumentException("Cannot reduce hol term: " + term.toString + " to fol as it is a higher order function or atom") // for cases of higher order atoms and functions
    }
  }
  // TODO - support generated function symbols by checking the arity from le and add the variables to the returned term. Right now only constants are supported
  object createExampleFOLConstant {
    def apply(le: LambdaExpression, css: ConstantStringSymbol) = FOLConst(css)
  }
}
