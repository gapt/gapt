package at.logic.gapt.expr

import at.logic.gapt.algorithms.rewriting.TermReplacement

/**
  * Created by sebastian on 3/21/16.
  */
object abstractTerm {
  def apply(exp: LambdaExpression)(t: LambdaExpression): Abs = {
    val x = rename(Var("x", t.exptype), freeVariables(exp))
    Abs(x,TermReplacement.apply(exp, t, x))
  }
}
