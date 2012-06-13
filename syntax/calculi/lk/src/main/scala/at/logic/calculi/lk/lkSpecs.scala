package at.logic.calculi.lk

import org.specs2.matcher._
import at.logic.calculi.lk.base.Sequent

package lkSpecs {

  import base.types.FSequent

  //A matcher which compares sequents using a multiset interpretation of the lists
  case class beMultisetEqual(s: Sequent) extends Matcher[Sequent]() {
    def apply[S <: Sequent](o: Expectable[S]) =
      result(s.multisetEquals(o.value), "successful multisetEquals", s.toString + " not multisetEquals " + o, o)
  }

  case class beSyntacticMultisetEqual(s: Sequent) extends Matcher[Sequent]() {
    def apply[S <: Sequent](o: Expectable[S]) =
      result(s.syntacticMultisetEquals(o.value), "successful syntactic multisetEquals", s.toString + " not syntactic multisetEquals " + o, o)
  }

}
