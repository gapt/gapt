package at.logic.gapt.proofs.ceres

import at.logic.gapt.expr.{ Expr, Formula }
import at.logic.gapt.proofs.{ Context, HOLSequent }
import at.logic.gapt.proofs.lk.LKProof

object extractStruct {
  def apply( p: LKProof ): Struct[Formula] =
    StructCreators.extract[Formula]( p )( Context() )
  def apply[Data]( p: LKProof, predicate: Formula => Boolean ): Struct[Formula] =
    StructCreators.extract[Formula]( p, predicate )( Context() )

}