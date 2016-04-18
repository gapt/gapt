package at.logic.gapt.proofs

import at.logic.gapt.expr.{ ClosedUnderSub, Substitution }

package object lksk {

  implicit val lkskClosedUnderSubst: ClosedUnderSub[LKskProof] = new ClosedUnderSub[LKskProof] {
    override def applySubstitution( sub: Substitution, arg: LKskProof ): LKskProof =
      lksk.applySubstitution( sub )( arg )
  }

}
