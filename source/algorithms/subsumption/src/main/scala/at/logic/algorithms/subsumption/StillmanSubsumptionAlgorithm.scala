/*
 * StillmanSubsumptionAlgorithm.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.algorithms.subsumption

import at.logic.algorithms.matching.MatchingAlgorithm
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.substitutions._
import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.language.hol._
import at.logic.language.fol.{Neg => FOLNeg, FOLFormula}
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.base.types._

trait StillmanSubsumptionAlgorithm[T <: LambdaExpression] extends SubsumptionAlgorithm {
  val matchAlg: MatchingAlgorithm[T]
  def subsumes(s1: FSequent, s2: FSequent): Boolean = subsumes_by(s1,s2).nonEmpty

  def subsumes_by(s1: FSequent, s2: FSequent) : Option[Substitution[T]] = {
    val left = s1._1.map(x => neg(x)) ++ s1._2.map(x => x)
    val right = s2._1.map(x => neg(x)) ++ s2._2.map(x => x)
    val lv = remove_doubles(left.foldLeft(List[Var]())((l,f) => vars(f,l)))
    val rv = remove_doubles(right.foldLeft(List[Var]())((l,f) => vars(f,l)))
    val renames = rv.filter(x=> lv.contains(x))
    var count = 0
    val vg = new VariableNameGenerator(() => {count = count+1; "vg_{"+count+"}"})
    val (newnames, _) = renames.foldLeft((List[Var](), lv++rv))((pair,x) => {
      val v = vg(x, pair._2)
      (v::pair._1, v::pair._2)
    }  )

    val sub = Substitution[LambdaExpression](renames zip newnames)
    val rsub = Substitution[LambdaExpression](newnames zip renames)


    ST(left, right.map(sub), Substitution[T](), newnames) match {
      case None => None
      case Some(subst) => Some(Substitution[T](subst.map.map(x => (x._1, rsub(x._2).asInstanceOf[T]))))
    }
  }

  def ST(ls1: Seq[LambdaExpression], ls2: Seq[LambdaExpression], sub: Substitution[T], restrictedDomain: List[Var])
   : Option[Substitution[T]] =
    ls1 match {
      case Nil => Some(sub) // first list is exhausted
      case x::ls =>
        val sx = sub(x.asInstanceOf[T]);
        //TODO: the original algorithm uses backtracking, this does not. check if this implementation is incomplete
        val nsubs = ls2.flatMap(t =>
          matchAlg.matchTerm(sx.asInstanceOf[T], sub(t.asInstanceOf[T]), restrictedDomain) match {
            case Some(sub2) =>
              val nsub : Substitution[T] = sub2.compose(sub)
              val st = ST(ls, ls2, nsub, restrictedDomain ++ nsub.map.flatMap(_._2.freeVariables))
              if (st.nonEmpty) st::Nil else Nil
            case _ => Nil
      })
      if (nsubs.nonEmpty) nsubs.head else None

  }

  // should be generic but right now supports only hol and fol
  private def neg(f: Formula) = if (f.isInstanceOf[FOLFormula]) FOLNeg(f.asInstanceOf[FOLFormula]) else Neg(f.asInstanceOf[HOLFormula])

  private def vars(e:LambdaExpression, vs : List[Var]) : List[Var] = e match {
    case Var(_:VariableSymbolA, _) => e.asInstanceOf[Var] :: vs
    case Var(_,_) => vs
    case App(s,t) => vars(s, vars(t, vs))
    case Abs(x,t) => vars(t,x::vs)
  }

  private def remove_doubles[T](l:List[T]) : List[T] = remove_doubles_(l.reverse).reverse
  private def remove_doubles_[T](l:List[T]) : List[T] = l match {
    case Nil => Nil
    case x::xs => if (xs contains x) remove_doubles_(xs) else x::remove_doubles_(xs)
  }
}
