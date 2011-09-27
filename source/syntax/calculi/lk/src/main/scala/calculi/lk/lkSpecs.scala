package at.logic.calculi.lk

import org.specs.matcher.Matcher
import at.logic.calculi.lk.base.Sequent

package lkSpecs {

import base.types.FSequent

// A matcher which compares sequents using a multiset interpretation of the lists
  case class beMultisetEqual(s: Sequent) extends Matcher[Sequent]() {
    def apply(o: => Sequent) =
      ( s.multisetEquals(o), "successful multisetEquals", s.toString + " not multisetEquals " + o.toString )
  }

  case class beSyntacticMultisetEqual(s: Sequent) extends Matcher[Sequent]() {
    def apply(o: => Sequent) =
      ( s.syntacticMultisetEquals(o), "successful syntactic multisetEquals", s.toString + " not syntactic multisetEquals " + o.toString )
  }

}
