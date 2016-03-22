package at.logic.gapt.expr

import at.logic.gapt.algorithms.rewriting.TermReplacement
import at.logic.gapt.expr.hol.HOLPosition

/**
  * Created by sebastian on 3/21/16.
  */

object replacementContext {
  def apply(exp: LambdaExpression, positions: Seq[LambdaPosition]): Abs = {
    require(positions.nonEmpty)
    val t = exp(positions.head)
    val x = rename(Var("x", t.exptype), freeVariables(exp))

    Abs(x, positions.foldLeft(exp){(acc,p) => acc.replace(p, x)})
  }

  def apply(exp: LambdaExpression, positions: Seq[HOLPosition])(implicit d: DummyImplicit): Abs = apply(exp, positions map {HOLPosition.toLambdaPosition(exp)})

  def abstractTerm(exp: LambdaExpression)(t: LambdaExpression): Abs = {
    val x = rename(Var("x", t.exptype), freeVariables(exp))
    Abs(x,TermReplacement(exp, t, x))
  }
}