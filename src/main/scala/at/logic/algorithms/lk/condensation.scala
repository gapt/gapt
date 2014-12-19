package at.logic.algorithms.lk

import at.logic.language.hol.HOLFormula
import at.logic.calculi.lk.base.FSequent

/**
 * Condensation implements the redundancy optimization technique of the same name, see also
 * Leitsch: The Resolution Calculus chapter 3.2
 */
object condensation extends condensation
class condensation {
  //TODO: implement

}

/**
 * Factoring removes duplicate literals from fsequents
 */
object factoring extends factoring
class factoring {
  def apply(fs : FSequent) : FSequent = {
    val ant = fs.antecedent.foldLeft(List[HOLFormula]())((a_, f) => if (a_.contains(f)) a_ else f::a_)
    val suc = fs.succedent.foldLeft(List[HOLFormula]())((a_, f) => if (a_.contains(f)) a_ else f::a_)
    FSequent(ant.reverse, suc.reverse)
  }

  def apply(l : List[FSequent]) : List[FSequent] = l.map(factoring.apply)
}
