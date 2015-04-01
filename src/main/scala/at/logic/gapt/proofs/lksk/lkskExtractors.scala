/*
 * lkskExtractors.scala
 *
 * This class contains extractors working for any lksk proof, no matter its
 * rules, so it should be updated with the additions of new rules to lksk.
 */

package at.logic.gapt.proofs.lksk

import at.logic.gapt.proofs.occurrences._
import at.logic.gapt.proofs.proofs._
import at.logic.gapt.language.hol._
import at.logic.gapt.proofs.lk.base.{ LKProof }
import at.logic.gapt.proofs.lk.{ WeakeningLeftRuleType, WeakeningRightRuleType }
import at.logic.gapt.proofs.lk.{ ForallLeftRuleType, ExistsRightRuleType, ForallRightRuleType, ExistsLeftRuleType }

// convenient extractors
object UnaryLKskProof {
  def unapply( proof: LKProof ) = proof match {
    case WeakeningLeftRule( up, r, p1 )      => Some( ( WeakeningLeftRuleType, up, r, Nil, p1 ) )
    case WeakeningRightRule( up, r, p1 )     => Some( ( WeakeningRightRuleType, up, r, Nil, p1 ) )
    case ForallSkLeftRule( up, r, a, p, _ )  => Some( ( ForallLeftRuleType, up, r, a :: Nil, p ) )
    case ExistsSkRightRule( up, r, a, p, _ ) => Some( ( ExistsRightRuleType, up, r, a :: Nil, p ) )
    case ForallSkRightRule( up, r, a, p, _ ) => Some( ( ForallRightRuleType, up, r, a :: Nil, p ) )
    case ExistsSkLeftRule( up, r, a, p, _ )  => Some( ( ExistsLeftRuleType, up, r, a :: Nil, p ) )
    case _                                   => None
  }
}
