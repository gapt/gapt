/*
 * longNormalForm.scala
 *
 * Transforms a function f: i0 -> ... -> in -> o into
 * \lambda x0:i0. ... \lambda xn:in f x0 ... xn
 * i.e. adds the lambda abstraction and new variables. 
 * Note that etaExpantion is applied only to expressions in beta-normal form.
 *
 * Implemented according to Definition 2.25 of Higher-Order Unification and 
 * Matching by Gilles Dowek (http://who.rocq.inria.fr/Gilles.Dowek/Publi/unification.ps)
 */

package at.logic.language.lambda

import symbols._
import types._
  
object longNormalForm {
  def apply(term: LambdaExpression) : LambdaExpression = apply(term, List())
  def apply(term: LambdaExpression, disallowedVars: List[Var]) : LambdaExpression = term match {
    case Var(_, exptype) => exptype match {
      case Ti => term
      case To => term
      case FunctionType(_, args) => {
        val binders: List[Var] = args.foldRight(List[Var]()) ( (z, acc) => {
          val newVar = Var("eta", z) // Creating a new var of appropriate type
          rename(newVar, disallowedVars ++ acc) :: acc // Rename if needed
        })
        val dv = disallowedVars ++ binders
        Abs(binders, App(term, binders.map((z => apply(z, dv)))))
      }
    }

    case App(m,n) => term.exptype match {
      case Ti => term
      case To => term
      case FunctionType(_, args) => {
        val binders: List[Var] = args.foldRight(List[Var]()) ( (z, acc) => {
          val newVar = Var("eta", z) // Creating a new var of appropriate type
          rename(newVar, disallowedVars ++ acc) :: acc // Rename if needed
        })
        val dv = disallowedVars ++ binders
        Abs(binders, App(App(m,apply(n, dv)), binders.map((z => apply(z, dv)))))
      }
    }

    case Abs(x,t) => Abs(x, apply(t, disallowedVars))
  }
}


