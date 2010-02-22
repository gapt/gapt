/*
 * Replacements.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.language.hol

import at.logic.language.hol._
import at.logic.language.lambda.typedLambdaCalculus._
import scala.collection.immutable._

package replacements {
  case class Replacement(position: List[Int], expression: HOLExpression) {
    def apply(exp: HOLExpression):HOLExpression = replace(position, exp)
    private def replace(pos: List[Int], exp: HOLExpression):HOLExpression = {
      (pos, exp)  match {
        case (1::rest, And(m,n)) => And(replace(rest, m.asInstanceOf[HOLFormula]).asInstanceOf[HOLFormula], n)
        case (2::rest, And(m,n)) => And(m, replace(rest, n.asInstanceOf[HOLFormula]).asInstanceOf[HOLFormula])
        case (1::rest, Or(m,n)) => Or(replace(rest, m.asInstanceOf[HOLFormula]).asInstanceOf[HOLFormula], n)
        case (2::rest, Or(m,n)) => Or(m, replace(rest, n.asInstanceOf[HOLFormula]).asInstanceOf[HOLFormula])
        case (1::rest, Imp(m,n)) => Imp(replace(rest, m.asInstanceOf[HOLFormula]).asInstanceOf[HOLFormula], n)
        case (2::rest, Imp(m,n)) => Imp(m, replace(rest, n.asInstanceOf[HOLFormula]).asInstanceOf[HOLFormula])
        case (1::rest, Neg(m)) => Neg(replace(rest, m.asInstanceOf[HOLFormula]).asInstanceOf[HOLFormula])
        case (1::rest, ExVar(v,m)) => ExVar(v, replace(rest, m.asInstanceOf[HOLFormula]).asInstanceOf[HOLFormula])
        case (1::rest, AllVar(v,m)) => AllVar(v, replace(rest, m.asInstanceOf[HOLFormula]).asInstanceOf[HOLFormula])
        case (n::rest, Atom(p,args)) => {
          val (firstArgs, arg::remainingArgs) = args.splitAt(n-1)
          Atom(p, firstArgs.asInstanceOf[List[HOLExpression]]:::(replace(rest, arg.asInstanceOf[HOLExpression])::remainingArgs.asInstanceOf[List[HOLExpression]]))
        }
        case (n::rest, AppN(f,args)) => {
          val (firstArgs, arg::remainingArgs) = args.splitAt(n-1)
          AppN(f, firstArgs:::(replace(rest, arg.asInstanceOf[HOLExpression])::remainingArgs)).asInstanceOf[HOLExpression]
        }
        case (1::rest, Abs(x,m)) => Abs(x, replace(rest,m.asInstanceOf[HOLExpression])).asInstanceOf[HOLExpression]
        case (Nil,_) => expression
        case _ => throw new IllegalArgumentException("Position ("+ pos +") does not exist in the expression (" + exp + ")")
      }
    }
  }
  object ImplicitConverters {
    implicit def convertPairToReplacement(pair: Tuple2[List[Int],HOLExpression]):Replacement = Replacement(pair._1, pair._2)
    implicit def convertReplacementToPair(rep: Replacement):Tuple2[List[Int],HOLExpression] = (rep.position, rep.expression)
  }
}
