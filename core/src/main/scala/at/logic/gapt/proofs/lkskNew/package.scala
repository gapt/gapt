package at.logic.gapt.proofs

import at.logic.gapt.expr.{ ClosedUnderSub, Substitution }

package object lkskNew {

  implicit val lkskClosedUnderSubst: ClosedUnderSub[LKskProof] = new ClosedUnderSub[LKskProof] {
    override def applySubstitution( sub: Substitution, arg: LKskProof ): LKskProof =
      lkskNew.applySubstitution( sub )( arg )
  }

}
