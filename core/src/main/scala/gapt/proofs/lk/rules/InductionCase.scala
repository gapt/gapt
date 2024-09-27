package gapt.proofs.lk.rules

import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.Var
import gapt.expr.ty.FunctionType
import gapt.proofs.SequentIndex
import gapt.proofs.lk.LKProof

/**
 * Proof that a given data type constructor c preserves a formula F:
 *
 * <pre>
 *                                  (π)
 * F(x,,1,,), F(x,,2,,), ..., F(x,,n,,), Γ :- Δ, F(c(x,,1,,,...,x,,n,,,y,,1,,,...,y,,n,,))
 * </pre>
 *
 * The variables x,,i,, and y,,i,, are eigenvariables; x,,i,, are the eigenvariables of the
 * same type as the inductive data type, y,,i,, are the other arguments of the constructor c.
 * They can come in any order in the constructor.
 *
 * @param proof  The LKProof ending in the sequent of this case.
 * @param constructor  The constructor c of the inductive data type that we're considering.
 * @param hypotheses  Indices of F(x,,1,,), ..., F(x,,n,,)
 * @param eigenVars  The eigenvariables of this case: x,,1,,, ..., x,,n,,, y,,1,,, ..., y,,n,,
 *                   (these need to correspond to the order in c)
 * @param conclusion  Index of F(c(x,,1,,,...,x,,n,,,y,,1,,,...,y,,n,,))
 */
case class InductionCase(proof: LKProof, constructor: Const, hypotheses: Seq[SequentIndex], eigenVars: Seq[Var], conclusion: SequentIndex) {
  val FunctionType(indTy, fieldTypes) = constructor.ty: @unchecked
  require(fieldTypes == eigenVars.map(_.ty))

  val hypVars: Seq[Var] = eigenVars filter { _.ty == indTy }
  require(hypotheses.size == hypVars.size)

  hypotheses foreach { hyp =>
    require(hyp.isAnt && proof.endSequent.isDefinedAt(hyp))
  }

  val term: Expr = constructor(eigenVars: _*)

  require(conclusion.isSuc && proof.endSequent.isDefinedAt(conclusion))
}
