
package at.logic.algorithms.expansionTrees

import at.logic.calculi.expansionTrees._
import at.logic.calculi.expansionTrees.multi.{WeakQuantifier => mWeakQuantifier, StrongQuantifier => mStrongQuantifier, And => mAnd, Or =>
mOr, Imp => mImp, Not => mNot, Atom => mAtom, MultiExpansionTree}
import at.logic.language.hol.{HOLExpression, HOLVar}

object compressQuantifiers {
  def apply(tree: ExpansionTree): MultiExpansionTree = tree match {
    case Atom(f) => mAtom(f)
    case Neg(t1) => mNot(compressQuantifiers(t1))
    case And(t1,t2) => mAnd(compressQuantifiers(t1), compressQuantifiers(t2))
    case Or(t1,t2) => mOr(compressQuantifiers(t1), compressQuantifiers(t2))
    case Imp(t1,t2) => mImp(compressQuantifiers(t1), compressQuantifiers(t2))
    case WeakQuantifier(f,is) => mWeakQuantifier(f, is.flatMap(x => compressWeak(compressQuantifiers(x._1),x._2)))
    case StrongQuantifier(f,v,t) => {val (sel, vars) = compressStrong(compressQuantifiers(t),v); mStrongQuantifier(f, vars,sel)}
  }

  private def compressStrong(tree: MultiExpansionTree, v: HOLVar): Tuple2[MultiExpansionTree, Seq[HOLVar]] = tree match {
    case mStrongQuantifier(_, vars, sel) => (sel, vars.+:(v))
    case _ => (tree, List(v))
  }

  private def compressWeak(tree: MultiExpansionTree, e: HOLExpression): Seq[Tuple2[MultiExpansionTree, Seq[HOLExpression]]] = tree match {
    case mWeakQuantifier(_, is) => is.map(x => (x._1, x._2.+:(e)))
    case _ => List((tree, List(e)))
  }
}
