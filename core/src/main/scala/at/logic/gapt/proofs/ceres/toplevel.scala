package at.logic.gapt.proofs.ceres

import at.logic.gapt.expr.Formula
import at.logic.gapt.proofs.lk.LKProof

object extractStruct {
  def apply( p: LKProof ): Struct[Formula] =
    StructCreators.extract[Formula]( p )
  def apply[Data]( p: LKProof, predicate: Formula => Boolean ): Struct[Formula] =
    StructCreators.extract[Formula]( p, predicate )

}