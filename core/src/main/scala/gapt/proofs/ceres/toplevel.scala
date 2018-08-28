package gapt.proofs.ceres

import gapt.expr.Formula
import gapt.proofs.context.Context
import gapt.proofs.lk.LKProof

object extractStruct {
  def apply( p: LKProof ): Struct =
    StructCreators.extract( p )( Context() )
  def apply[Data]( p: LKProof, predicate: Formula => Boolean ): Struct =
    StructCreators.extract( p, predicate )( Context() )

}