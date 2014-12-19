/*
 * lkExtractors.scala
 *
 * This class contains extractors working for any lk proof, no matter its rules, so it should be updated with the additions of new rules to lk
 */

package at.logic.calculi.lk

import base._

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
    case ForallLeftRule(up, r, a, p, _) => Some((ForallLeftRuleType, up, r, a::Nil, p))
    case ExistsRightRule(up, r, a, p, _) => Some((ExistsRightRuleType, up, r, a::Nil, p))
    case ForallRightRule(up, r, a, p, _) => Some((ForallRightRuleType, up, r, a::Nil, p))
    case ExistsLeftRule(up, r, a, p, _) => Some((ExistsLeftRuleType, up, r, a::Nil, p))
    case DefinitionLeftRule(up, r, a, p) => Some((DefinitionLeftRuleType, up, r, a::Nil, p))
    case DefinitionRightRule(up, r, a, p) => Some((DefinitionRightRuleType, up, r, a::Nil, p))
//    case UnaryEquationLeft1Rule(up, r, a1, a2,_, p) => Some((UnaryEquationLeft1RuleType, up, r, a1::a2 ::Nil, p))
//    case UnaryEquationLeft2Rule(up, r, a1, a2,_, p) => Some((UnaryEquationLeft2RuleType, up, r, a1::a2 ::Nil, p))
//    case UnaryEquationRight1Rule(up, r, a1, a2,_, p) => Some((UnaryEquationRight1RuleType, up, r, a1::a2 ::Nil, p))
//    case UnaryEquationRight2Rule(up, r, a1, a2,_, p) => Some((UnaryEquationRight2RuleType, up, r, a1::a2 ::Nil, p))
    case _ => None
  }
}

object BinaryLKProof {
  def unapply(proof: LKProof) = proof match {
    case CutRule(up1, up2, r, a1, a2) => Some((CutRuleType, up1, up2, r, a1, a2, None))
    case AndRightRule(up1, up2, r, a1, a2, p) => Some((AndRightRuleType, up1, up2, r, a1, a2, Some(p)))
    case OrLeftRule(up1, up2, r, a1, a2, p) => Some((OrLeftRuleType, up1, up2, r, a1, a2, Some(p)))
    case ImpLeftRule(up1, up2, r, a1, a2, p) => Some((ImpLeftRuleType, up1, up2, r, a1, a2, Some(p)))
    case EquationLeft1Rule(up1, up2, r, a1, a2,_, p) => Some((EquationLeft1RuleType, up1, up2, r, a1, a2, Some(p)))
    case EquationLeft2Rule(up1, up2, r, a1, a2,_, p) => Some((EquationLeft2RuleType, up1, up2, r, a1, a2, Some(p)))
    case EquationRight1Rule(up1, up2, r, a1, a2,_, p) => Some((EquationRight1RuleType, up1, up2, r, a1, a2, Some(p)))
    case EquationRight2Rule(up1, up2, r, a1, a2,_, p) => Some((EquationRight2RuleType, up1, up2, r, a1, a2, Some(p)))
    case _ => None
  }
}

