/*
 * TermNormalizer.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.normalization

import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.symbols._
import scala.collection.mutable.Map

// rename variables to a fixed form
object TermNormalizer {
  /*
  def apply(t: LambdaExpression, map: Map[Var,Var], nextId: => Int): LambdaExpression = t match {
    case v1 @ Var(VariableStringSymbol(_),_) => map.getOrElseUpdate(v1.asInstanceOf[Var], normalizeVar(v1.asInstanceOf[Var], nextId))
    case v1: Var => v1
    case App(e1, arg1) => App(apply(e1,map, nextId), apply(arg1,map, nextId))
    case AbsInScope(v, e1) => Abs(apply(v,map, nextId).asInstanceOf[Var], apply(e1,map, nextId))
  }

  private def normalizeVar(v: Var, nextId: => Int): Var = v match {
    // we dont need to take care of dbIndices here as Abs recomputes them anyway
    case Var(VariableStringSymbol(_),_) => v.factory.createVar(VariableStringSymbol("x_{" + nextId + "}"), v.exptype)
    // other cases should be treated when they are implemented
  } */
}
