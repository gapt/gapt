package at.logic.gapt.proofs.lk.base

import at.logic.gapt.proofs.HOLSequent
import org.specs2.matcher._

case class beSyntacticMultisetEqual( s: OccSequent ) extends Matcher[OccSequent]() {
  def apply[S <: OccSequent]( o: Expectable[S] ) =
    result( s.syntacticMultisetEquals( o.value ), "successful syntactic multisetEquals", s.toString + " not syntactic multisetEquals " + o.value, o )
}

case class beSyntacticFSequentEqual( s: HOLSequent ) extends Matcher[HOLSequent]() {
  def apply[S <: HOLSequent]( o: Expectable[S] ) =
    result( s.multiSetEquals( o.value ), "successful syntactic multisetEquals", s.toString + " not the same multiset as fsequent " + o.value, o )
}

