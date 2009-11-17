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



//object Replacements {
//    case class Replacement[A](position: List[Int], expression: LambdaExpression[A]) {
//
//        def apply(exp: LambdaExpression[A]):LambdaExpression[A] = replace(position, exp)
//
//        private def replace(pos: List[Int], exp: LambdaExpression[A]):LambdaExpression[A] = {
//            (pos, exp)  match {
//                case (1::rest, App(m,n)) => App(replace(rest, m), n)
//                case (2::rest, App(m,n)) => App(m, replace(rest, n))
//                case (1::rest, Abs(x,m)) => Abs(x, replace(rest,m))
//                case (Nil,_) => expression
//                case _ => throw new IllegalArgumentException("Position ("+ pos +") does not exist in the expression (" + exp + ")")
//            }
//        }
//    }
//    object ImplicitConverters {
//        implicit def convertPairToReplacement(pair: Tuple2[List[Int],LambdaExpression[_]]):Replacement = Replacement(pair._1, pair._2)
//        implicit def convertReplacementToPair(rep: Replacement):Tuple2[List[Int],LambdaExpression[_]] = (rep.position, sub.expression)
//    }
//}
