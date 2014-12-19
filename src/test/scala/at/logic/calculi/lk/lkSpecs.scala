package at.logic.calculi.lk.base

import org.specs2.matcher._

case class beSyntacticMultisetEqual(s: Sequent) extends Matcher[Sequent]() {
  def apply[S <: Sequent](o: Expectable[S]) =
    result(s.syntacticMultisetEquals(o.value), "successful syntactic multisetEquals", s.toString + " not syntactic multisetEquals " + o.value, o)
}

case class beSyntacticFSequentEqual(s: FSequent) extends Matcher[FSequent]() {
  def apply[S <: FSequent](o: Expectable[S]) =
    result(s.multiSetEquals(o.value), "successful syntactic multisetEquals", s.toString + " not the same multiset as fsequent " + o.value, o)
}

