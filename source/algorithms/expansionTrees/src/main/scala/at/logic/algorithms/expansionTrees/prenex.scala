package at.logic.algorithms.expansionTrees

import at.logic.calculi.expansionTrees.multi._
import at.logic.language.hol.{HOLExpression, HOLVar}

object containsQuantifier {
  def apply(tree: MultiExpansionTree) : Boolean = tree match {
    case Atom(_) => false
    case Not(t1) => containsQuantifier(t1)
    case And(t1,t2) => containsQuantifier(t1) || containsQuantifier(t2)
    case Or(t1,t2) => containsQuantifier(t1) || containsQuantifier(t2)
    case Imp(t1,t2) => containsQuantifier(t1) || containsQuantifier(t2)
    case WeakQuantifier(_,_) => true
    case StrongQuantifier(_,_,_) => true
  }
}

object isPrenex {
  def apply(tree: MultiExpansionTree): Boolean = tree match {
    case Atom(_) => true
    case Not(t1) => !containsQuantifier(t1)
    case And(t1,t2) => !containsQuantifier(t1) && !containsQuantifier(t2)
    case Or(t1,t2) => !containsQuantifier(t1) && !containsQuantifier(t2)
    case Imp(t1,t2) => !containsQuantifier(t1) && !containsQuantifier(t2)
    case WeakQuantifier(_,is) => is.forall(i => isPrenex(i._1))
    case StrongQuantifier(_,_,t) => isPrenex(t)
  }
}


