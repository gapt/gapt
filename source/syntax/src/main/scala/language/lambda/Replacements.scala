/*
 * Substitutions.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.lambda

import Symbols._
import TypedLambdaCalculus._
import scala.collection.immutable._



object Replacements {
    case class Replacement[A <: Lambda](position: List[Int], expression: LambdaExpression[A]) {

        def apply(exp: LambdaExpression[A])(implicit factory1: AbsFactory[A], factory2: AppFactory[A]):LambdaExpression[A] = replace(position, exp)

        private def replace(pos: List[Int], exp: LambdaExpression[A])(implicit factory1: AbsFactory[A], factory2: AppFactory[A]):LambdaExpression[A] = {
            (pos, exp)  match {
                case (1::rest, App(m,n)) => App(replace(rest, m.asInstanceOf[LambdaExpression[A]]), n.asInstanceOf[LambdaExpression[A]])
                case (2::rest, App(m,n)) => App(m.asInstanceOf[LambdaExpression[A]], replace(rest, n.asInstanceOf[LambdaExpression[A]]))
                case (1::rest, Abs(x,m)) => Abs(x.asInstanceOf[Var[A]], replace(rest,m.asInstanceOf[LambdaExpression[A]]))
                case (Nil,_) => expression
                case _ => throw new IllegalArgumentException("Position ("+ pos +") does not exist in the expression (" + exp + ")")
            }
        }
    }
    object ImplicitConverters {
        implicit def convertPairToReplacement[A <: Lambda](pair: Tuple2[List[Int],LambdaExpression[A]]):Replacement[A] = Replacement(pair._1, pair._2)
        implicit def convertReplacementToPair[A <: Lambda](rep: Replacement[A]):Tuple2[List[Int],LambdaExpression[A]] = (rep.position, rep.expression)
    }
}
