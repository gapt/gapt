package gapt.proofs.ceres

import gapt.expr.formula.Formula
import gapt.proofs.context.Context
import gapt.proofs.lk.LKProof

object extractStruct {
  def apply(p: LKProof): Struct =
    apply(p, CERES.skipNothing)
  def apply(p: LKProof, predicate: Formula => Boolean): Struct =
    StructCreators.extract(p, predicate)(Context())

}
