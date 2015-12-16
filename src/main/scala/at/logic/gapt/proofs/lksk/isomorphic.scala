package at.logic.gapt.proofs.lksk

import at.logic.gapt.proofs.lkOld.base.{ LKProof, NullaryLKProof }
import at.logic.gapt.proofs.lkOld.{ BinaryLKProof, UnaryLKProof }
import at.logic.gapt.proofs.proofs.RuleTypeA

/**
 * Created by marty on 8/25/14.
 */
object rule_isomorphic extends rule_isomorphic
class rule_isomorphic {
  val nLine = sys.props( "line.separator" )
  def apply( p1: LKProof, p2: LKProof, pred: ( RuleTypeA, RuleTypeA ) => Boolean ): Boolean =
    ( p1, p2 ) match {
      case ( a1: NullaryLKProof, a2: NullaryLKProof ) =>
        pred( a1.rule, a2.rule )
      case ( UnaryLKProof( t1, up1, _, _, _ ), UnaryLKProof( t2, up2, _, _, _ ) ) =>
        pred( t1, t2 ) && apply( up1, up2, pred )
      case ( UnaryLKProof( t1, up1, _, _, _ ), UnaryLKskProof( t2, up2, _, _, _ ) ) =>
        pred( t1, t2 ) && apply( up1, up2, pred )
      case ( UnaryLKskProof( t1, up1, _, _, _ ), UnaryLKProof( t2, up2, _, _, _ ) ) =>
        pred( t1, t2 ) && apply( up1, up2, pred )
      case ( UnaryLKskProof( t1, up1, _, _, _ ), UnaryLKskProof( t2, up2, _, _, _ ) ) =>
        pred( t1, t2 ) && apply( up1, up2, pred )
      case ( BinaryLKProof( t1, up1a, up1b, _, _, _, _ ), BinaryLKProof( t2, up2a, up2b, _, _, _, _ ) ) =>
        pred( t1, t2 ) && apply( up1a, up2a, pred ) && apply( up1b, up2b, pred )
      case _ =>
        throw new Exception( "can not compare " + p1.rule + " and " + p2.rule + nLine + "p1= " + p1 + nLine + "p2= " + p2 )
    }
}
