package gapt.proofs.ceres

import gapt.expr.{ Expr, Formula }
import gapt.proofs.{ Context, HOLSequent }
import gapt.proofs.lk.LKProof

object extractStruct {
  def apply( p: LKProof ): Struct =
    StructCreators.extract( p )( Context() )
  def apply[Data]( p: LKProof, predicate: Formula => Boolean ): Struct =
    StructCreators.extract( p, predicate )( Context() )

}