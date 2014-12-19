package at.logic.algorithms.lk

import at.logic.calculi.lk.base.{NullaryLKProof, LKProof}
import at.logic.calculi.lk.{Axiom, BinaryLKProof, UnaryLKProof}
import at.logic.calculi.proofs.RuleTypeA

/**
 * Created by marty on 8/25/14.
 */
object rule_isomorphic extends rule_isomorphic

/**
 * Checks if two proof have the same branching structure.
 * @note does not work for LKsk proofs
 */
class rule_isomorphic {
  /**
   * Checks if the lk proofs p1 and p2 are equal modulo the predicate pred. The branching
   * structure must be kept intact.
   * @param p1 an LK proof
   * @param p2 the LK proof to compare to
   * @param pred a predicate returning true whenever the two rule types should be considered isomorphic
   * @return true iff p1 and p2 are ismorphic modulo pred
   */
  def apply(p1 : LKProof, p2 : LKProof, pred : (RuleTypeA, RuleTypeA) => Boolean) : Boolean =
    (p1,p2) match {
      case (a1 : NullaryLKProof, a2 : NullaryLKProof) =>
        pred(a1.rule, a2.rule)
      case (UnaryLKProof(t1,up1,_,_,_), UnaryLKProof(t2, up2,_,_,_)) =>
        pred(t1,t2) && apply(up1,up2, pred)
      case (BinaryLKProof(t1,up1a,up1b, _ ,_,_,_), BinaryLKProof(t2, up2a, up2b,_ ,_,_,_)) =>
        pred(t1,t2) && apply(up1a,up2a, pred) && apply(up1b,up2b, pred)
      case _ =>
        false
  }
}
