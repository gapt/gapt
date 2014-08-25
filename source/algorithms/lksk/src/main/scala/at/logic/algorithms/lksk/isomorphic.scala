package at.logic.algorithms.lksk

import at.logic.calculi.lk.base.{NullaryLKProof, LKProof}
import at.logic.calculi.lk.{Axiom, BinaryLKProof, UnaryLKProof}
import at.logic.calculi.proofs.RuleTypeA
import at.logic.calculi.lksk.UnaryLKskProof

/**
 * Created by marty on 8/25/14.
 */
object rule_isomorphic extends rule_isomorphic
class rule_isomorphic {
  def apply(p1 : LKProof, p2 : LKProof, pred : (RuleTypeA, RuleTypeA) => Boolean) : Boolean =
    (p1,p2) match {
      case (a1 : NullaryLKProof, a2 : NullaryLKProof) =>
        pred(a1.rule, a2.rule)
      case (UnaryLKProof(t1,up1,_,_,_), UnaryLKProof(t2, up2,_,_,_)) =>
        pred(t1,t2) && apply(up1,up2, pred)
      case (UnaryLKProof(t1,up1,_,_,_), UnaryLKskProof(t2, up2,_,_,_)) =>
        pred(t1,t2) && apply(up1,up2, pred)
      case (UnaryLKskProof(t1,up1,_,_,_), UnaryLKProof(t2, up2,_,_,_)) =>
        pred(t1,t2) && apply(up1,up2, pred)
      case (UnaryLKskProof(t1,up1,_,_,_), UnaryLKskProof(t2, up2,_,_,_)) =>
        pred(t1,t2) && apply(up1,up2, pred)
      case (BinaryLKProof(t1,up1a,up1b, _ ,_,_,_), BinaryLKProof(t2, up2a, up2b,_ ,_,_,_)) =>
        pred(t1,t2) && apply(up1a,up2a, pred) && apply(up1b,up2b, pred)
      case _ =>
        throw new Exception("can not compare "+p1.rule+" and "+p2.rule+"\np1= "+p1+"\np2= "+p2)
    }
}
