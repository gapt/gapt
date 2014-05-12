/*
 * Replacements.scala
 *
 */

package at.logic.language.hol.replacements

import at.logic.language.hol._

  
case class Replacement(position: List[Int], expression: HOLExpression) {
  def apply(exp: HOLExpression):HOLExpression = replace(position, exp)

  // To avoid all the casting...
  private def replace(pos: List[Int], f: HOLFormula) : HOLFormula = replace(pos, f.asInstanceOf[HOLExpression]).asInstanceOf[HOLFormula]

  private def replace(pos: List[Int], exp: HOLExpression):HOLExpression = {
    (pos, exp)  match {
      case (1::rest, And(m,n)) => And(replace(rest, m), n)
      case (2::rest, And(m,n)) => And(m, replace(rest, n))
      case (1::rest, Or(m,n)) => Or(replace(rest, m), n)
      case (2::rest, Or(m,n)) => Or(m, replace(rest, n))
      case (1::rest, Imp(m,n)) => Imp(replace(rest, m), n)
      case (2::rest, Imp(m,n)) => Imp(m, replace(rest, n))
      case (1::rest, Neg(m)) => Neg(replace(rest, m))
      case (1::rest, ExVar(v,m)) => ExVar(v, replace(rest, m))
      case (1::rest, AllVar(v,m)) => AllVar(v, replace(rest, m))
      case (1::rest, Equation(m,n)) => Equation(replace(rest, m), n)
      case (2::rest, Equation(m,n)) => Equation(m, replace(rest, n))
      case (n::rest, Atom(p: HOLConst, args)) => {
        val (firstArgs, arg::remainingArgs) = args.splitAt(n-1)
        Atom(p, firstArgs:::(replace(rest, arg)::remainingArgs))
      }
      case (n::rest, Atom(p: HOLVar, args)) => {
        val (firstArgs, arg::remainingArgs) = args.splitAt(n-1)
        Atom(p, firstArgs:::(replace(rest, arg)::remainingArgs))
      }
      case (n::rest, Function(p: HOLConst, args, t)) => {
        val (firstArgs, arg::remainingArgs) = args.splitAt(n-1)
        Function(p, firstArgs:::(replace(rest, arg)::remainingArgs))
      }
      case (n::rest, Function(p: HOLVar, args, t)) => {
        val (firstArgs, arg::remainingArgs) = args.splitAt(n-1)
        Function(p, firstArgs:::(replace(rest, arg)::remainingArgs))
      }
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
      case ExVar(_, exp) => (curPos, t)::recApply(exp, curPos ::: List(1))
      case AllVar(_, exp) => (curPos, t)::recApply(exp, curPos ::: List(1))
      case Atom(_, args) => (curPos, t)::args.zipWithIndex.flatMap(el => recApply(el._1.asInstanceOf[HOLExpression], curPos ::: List(el._2+1)))
      case Function(_, args, _) => (curPos, t)::args.zipWithIndex.flatMap(el => recApply(el._1.asInstanceOf[HOLExpression], curPos ::: List(el._2+1)))
      //case Abs(_, exp) => (curPos, t)::recApply(exp.asInstanceOf[HOLExpression], curPos ::: List(1))
    }
}

object getAtPosition {
  def apply(expression: HOLExpression, pos: List[Int]): HOLExpression = (expression, pos) match {
    case (t, Nil) => t
    case (HOLVar(_,_), n) => throw new IllegalArgumentException("trying to obtain a subterm of a variable at position: " + n)
    case (HOLConst(_,_), n) => throw new IllegalArgumentException("trying to obtain a subterm of a constant at position: " + n)
    case (AllVar(_, exp), 1::rest) => getAtPosition(exp, rest)
    case (ExVar(_, exp), 1::rest) => getAtPosition(exp, rest)
    case (Atom(_, args), n::rest) => getAtPosition(args(n-1).asInstanceOf[HOLExpression], rest)
    case (Function(_, args, _), n::rest) => getAtPosition(args(n-1).asInstanceOf[HOLExpression], rest)
    //case (Abs(_, exp), 1::rest) => getAtPosition(exp.asInstanceOf[HOLExpression], rest)
    case (_, n::rest) => throw new IllegalArgumentException("trying to obtain a subterm of " + expression + " at position: " + n)
  }
}

/*object ImplicitConverters {
  implicit def convertPairToReplacement(pair: Tuple2[List[Int],HOLExpression]):Replacement = Replacement(pair._1, pair._2)
  implicit def convertReplacementToPair(rep: Replacement):Tuple2[List[Int],HOLExpression] = (rep.position, rep.expression)
}*/
