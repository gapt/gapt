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
        case (1::rest, And(m,n)) => And(replace(rest, m).asInstanceOf[HOLFormula], n)
        case (2::rest, And(m,n)) => And(m, replace(rest, n).asInstanceOf[HOLFormula])
        case (1::rest, Or(m,n)) => Or(replace(rest, m).asInstanceOf[HOLFormula], n)
        case (2::rest, Or(m,n)) => Or(m, replace(rest, n).asInstanceOf[HOLFormula])
        case (1::rest, Imp(m,n)) => Imp(replace(rest, m).asInstanceOf[HOLFormula], n)
        case (2::rest, Imp(m,n)) => Imp(m, replace(rest, n).asInstanceOf[HOLFormula])
        case (1::rest, Neg(m)) => Neg(replace(rest, m).asInstanceOf[HOLFormula])
        case (1::rest, ExVar(v,m)) => ExVar(v, replace(rest, m).asInstanceOf[HOLFormula])
        case (1::rest, AllVar(v,m)) => AllVar(v, replace(rest, m).asInstanceOf[HOLFormula])
        case (1::rest, Equation(m,n)) => Equation(replace(rest, m), n)
        case (2::rest, Equation(m,n)) => Equation(m, replace(rest, n))
        case (n::rest, app@ Atom(p,args)) => {
          val (firstArgs, arg::remainingArgs) = args.splitAt(n-1)
          Atom(p, firstArgs.asInstanceOf[List[HOLExpression]]:::(replace(rest, arg.asInstanceOf[HOLExpression])::remainingArgs.asInstanceOf[List[HOLExpression]]))
        }
        case (n::rest, app@ Function(p,args,t)) => {
          val (firstArgs, arg::remainingArgs) = args.splitAt(n-1)
          Function(p, firstArgs.asInstanceOf[List[HOLExpression]]:::(replace(rest, arg.asInstanceOf[HOLExpression])::remainingArgs.asInstanceOf[List[HOLExpression]]),t)
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

  // return all positions except var positions
  object getAllPositions {
    def apply(expression: HOLExpression): List[Tuple2[List[Int], HOLExpression]] = recApply(expression, List())
    def recApply(t: HOLExpression, curPos: List[Int]): List[Tuple2[List[Int], HOLExpression]] = t match {
        case HOLVar(_,_) => Nil // no need to paramodulate on variable positions
        case HOLConst(_,_) => (curPos, t)::Nil
        case Quantifier(_, _, exp) => (curPos, t)::recApply(exp, curPos ::: List(1))
        case Atom(_, args) => (curPos, t)::args.zipWithIndex.flatMap(el => recApply(el._1.asInstanceOf[HOLExpression], curPos ::: List(el._2+1)))
        case Function(_, args, _) => (curPos, t)::args.zipWithIndex.flatMap(el => recApply(el._1.asInstanceOf[HOLExpression], curPos ::: List(el._2+1)))
        case Abs(_, exp) => (curPos, t)::recApply(exp.asInstanceOf[HOLExpression], curPos ::: List(1))
      }
  }

  object getAtPosition {
    def apply(expression: HOLExpression, pos: List[Int]): HOLExpression = (expression, pos) match {
      case (t, Nil) => t
      case (HOLVar(_,_), n) => throw new IllegalArgumentException("trying to obtain a subterm of a variable at position: " + n)
      case (HOLConst(_,_), n) => throw new IllegalArgumentException("trying to obtain a subterm of a constant at position: " + n)
      case (Quantifier(_, _, exp), 1::rest) => getAtPosition(exp, rest)
      case (Atom(_, args), n::rest) => getAtPosition(args(n-1).asInstanceOf[HOLExpression], rest)
      case (Function(_, args, _), n::rest) => getAtPosition(args(n-1).asInstanceOf[HOLExpression], rest)
      case (Abs(_, exp), 1::rest) => getAtPosition(exp.asInstanceOf[HOLExpression], rest)
      case (_, n::rest) => throw new IllegalArgumentException("trying to obtain a subterm of " + expression + " at position: " + n)
    }
  }

  object ImplicitConverters {
    implicit def convertPairToReplacement(pair: Tuple2[List[Int],HOLExpression]):Replacement = Replacement(pair._1, pair._2)
    implicit def convertReplacementToPair(rep: Replacement):Tuple2[List[Int],HOLExpression] = (rep.position, rep.expression)
  }
}
