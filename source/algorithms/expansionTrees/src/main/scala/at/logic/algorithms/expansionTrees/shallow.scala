package at.logic.algorithms.expansionTrees

import at.logic.calculi.expansionTrees.multi._
import at.logic.language.hol.{Atom => HOLAtom, Neg => HOLNot, And => HOLAnd, Or => HOLOr, Imp => HOLImp}
import at.logic.language.hol.HOLFormula

object shallow {
  def apply(tree: MultiExpansionTree): HOLFormula = tree match {
    case Atom(f) => f
    case Not(t1) => HOLNot(shallow(t1))
    case And(t1,t2) => HOLAnd(shallow(t1), shallow(t2))
    case Or(t1,t2) => HOLOr(shallow(t1), shallow(t2))
    case Imp(t1,t2) => HOLImp(shallow(t1), shallow(t2))
    case WeakQuantifier(f,_) => f
    case StrongQuantifier(f,_,_) => f
  }
}
