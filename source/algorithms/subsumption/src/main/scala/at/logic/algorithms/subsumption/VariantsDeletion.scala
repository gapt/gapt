/*
 * VariantsDeletion.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.subsumption

import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.symbols._
import scala.collection.mutable

object VariantsDeletion {
  def isVariantOf(t1: LambdaExpression, t2: LambdaExpression): Boolean = isVariantOf(t1,t2,mutable.Map())
  def isVariantOf(t1: LambdaExpression, t2: LambdaExpression, map: mutable.Map[Var,Var]): Boolean = (t1,t2) match {
    case (v1 @ Var(VariableStringSymbol(_),_), v2 @ Var(VariableStringSymbol(_),_))
      if (v1.asInstanceOf[Var].isFree && v2.asInstanceOf[Var].isFree) =>
      map.getOrElseUpdate(v1.asInstanceOf[Var],v2.asInstanceOf[Var]) == v2
    case (v1: Var, v2: Var) => v1 == v2
    case (App(e1, arg1), App(e2, arg2)) => isVariantOf(e1,e2,map) && isVariantOf(arg1,arg2,map)
    case (Abs(_, e1), Abs(_, e2)) => isVariantOf(e1,e2,map)
    case _ => false
  }
  def removeVariants(col: Iterable[LambdaExpression]): List[LambdaExpression] = col.foldLeft(Nil: List[LambdaExpression])((ls, el) => if (ls.exists(x => isVariantOf(x,el))) ls else (el::ls))
}
