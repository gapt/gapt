/*
 * lkExtractors.scala
 *
 * This class contains extractors working for any lk proof, no matter its rules, so it should be updated with the additions of new rules to lk
 */

package at.logic.calculi.lk

import at.logic.calculi.occurrences._
import at.logic.language.hol.propositions._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.utils.ds.trees._
import scala.collection.immutable.Set
import scala.collection.mutable.HashMap
import propositionalRules._
import quantificationRules._

package lkExtractors {
 // convenient extractors
  object UnaryLKProof {
    def unapply(proof: LKProof) = proof match {
      case WeakeningLeftRule(up, r, p1) => Some((WeakeningLeftRuleType, up, r, Nil, p1))
      case WeakeningRightRule(up, r, p1) => Some((WeakeningRightRuleType, up, r, Nil, p1))
      case ContractionLeftRule(up, r, a1, a2, p1) => Some((ContractionLeftRuleType, up, r, a1::a2::Nil, p1))
      case ContractionRightRule(up, r, a1, a2, p1) => Some((ContractionRightRuleType, up, r, a1::a2::Nil, p1))
      case AndLeft1Rule(up, r, a, p) => Some((AndLeft1RuleType, up, r, a::Nil, p))
      case AndLeft2Rule(up, r, a, p) => Some((AndLeft2RuleType, up, r, a::Nil, p))
      case OrRight1Rule(up, r, a, p) => Some((OrRight1RuleType, up, r, a::Nil, p))
      case OrRight2Rule(up, r, a, p) => Some((OrRight2RuleType, up, r, a::Nil, p))
      case ImpRightRule(up, r, a1, a2, p) => Some((ImpRightRuleType, up, r, a1::a2::Nil, p))
      case NegLeftRule(up, r, a, p) => Some((NegLeftRuleType, up, r, a::Nil, p))
      case NegRightRule(up, r, a, p) => Some((NegRightRuleType, up, r, a::Nil, p))
      case _ => None
    }
  }

  object BinaryLKProof {
    def unapply(proof: LKProof) = proof match {
      case CutRule(up1, up2, r, a1, a2) => Some((CutRuleType, up1, up2, r, a1, a2, None))
      case AndRightRule(up1, up2, r, a1, a2, p) => Some((AndRightRuleType, up1, up2, r, a1, a2, Some(p)))
      case OrLeftRule(up1, up2, r, a1, a2, p) => Some((OrLeftRuleType, up1, up2, r, a1, a2, Some(p)))
      case ImpLeftRule(up1, up2, r, a1, a2, p) => Some((ImpLeftRuleType, up1, up2, r, a1, a2, Some(p)))
      case _ => None
    }
  }

}
