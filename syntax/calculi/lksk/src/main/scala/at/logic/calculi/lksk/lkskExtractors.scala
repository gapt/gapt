/*
 * lkExtractors.scala
 *
 * This class contains extractors working for any lk proof, no matter its rules, so it should be updated with the additions of new rules to lk
 */

package at.logic.calculi.lksk

import at.logic.calculi.occurrences._
import at.logic.calculi.proofs._
import at.logic.language.hol._
import at.logic.language.lambda.typedLambdaCalculus._
import scala.collection.immutable.Set
import scala.collection.mutable.HashMap
import base._
import at.logic.calculi.lk.base.{LKProof}
import at.logic.calculi.lk.propositionalRules.{WeakeningLeftRuleType, WeakeningRightRuleType}
import at.logic.calculi.lk.quantificationRules.{ForallLeftRuleType, ExistsRightRuleType, ForallRightRuleType, ExistsLeftRuleType}

package lkskExtractors {
 // convenient extractors
  object UnaryLKskProof {
    def unapply(proof: LKProof) = proof match {
      case WeakeningLeftRule(up, r, p1) => Some((WeakeningLeftRuleType, up, r, Nil, p1))
      case WeakeningRightRule(up, r, p1) => Some((WeakeningRightRuleType, up, r, Nil, p1))
      case ForallSkLeftRule(up, r, a, p, _) => Some((ForallLeftRuleType, up, r, a::Nil, p))
      case ExistsSkRightRule(up, r, a, p, _) => Some((ExistsRightRuleType, up, r, a::Nil, p))
      case ForallSkRightRule(up, r, a, p, _) => Some((ForallRightRuleType, up, r, a::Nil, p))
      case ExistsSkLeftRule(up, r, a, p, _) => Some((ExistsLeftRuleType, up, r, a::Nil, p))
      case _ => None
    }
  }
}
