package at.logic.calculi.lk

import at.logic.language.hol.HigherOrderLogic.HOL
import org.specs.matcher.Matcher
import at.logic.calculi.lk.LK.Sequent

object LKSpecs {
  // A matcher which compares sequents using a multiset interpretation of the lists
  case class beMultisetEqual(s: Sequent) extends Matcher[Sequent]() {
    def apply(o: => Sequent) =
      ( s.multisetEquals(o), "successful multisetEquals", s.toString + " not multisetEquals " + o.toString )
  }
}
