package gapt.proofs.lk.rules.macros

import gapt.expr.BetaReduction
import gapt.expr.Expr
import gapt.expr.formula.Formula
import gapt.expr.formula.hol.instantiate
import gapt.proofs.SequentConnector
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.ForallLeftRule

object ForallLeftBlock {
  /**
   * Applies the ForallLeft-rule n times.
   * This method expects a formula main with
   * a quantifier block, and a proof s1 which has a fully
   * instantiated version of main on the left side of its
   * bottommost sequent.
   *
   * The rule:
   * <pre>
   *                (π)
   *  A[x1\term1,...,xN\termN], Γ :- Δ
   * ---------------------------------- (∀_l x n)
   *       ∀ x1,..,xN.A, Γ :- Δ
   * </pre>
   *
   * @param subProof The top proof with (sL, A[x1\term1,...,xN\termN] :- sR) as the bottommost sequent.
   * @param main A formula of the form (Forall x1,...,xN.A).
   * @param terms The list of terms with which to instantiate main. The caller of this
   * method has to ensure the correctness of these terms, and, specifically, that
   * A[x1\term1,...,xN\termN] indeed occurs at the bottom of the proof π.
   */
  def apply( subProof: LKProof, main: Formula, terms: Seq[Expr] ): LKProof =
    withSequentConnector( subProof, main, terms )._1

  /**
   * Applies the ForallLeft-rule n times.
   * This method expects a formula main with
   * a quantifier block, and a proof s1 which has a fully
   * instantiated version of main on the left side of its
   * bottommost sequent.
   *
   * The rule:
   * <pre>
   *                (π)
   *  A[x1\term1,...,xN\termN], Γ :- Δ
   * ---------------------------------- (∀_l x n)
   *       ∀ x1,..,xN.A, Γ :- Δ
   * </pre>
   *
   *
   *
   * @param subProof The top proof with (sL, A[x1\term1,...,xN\termN] :- sR) as the bottommost sequent.
   * @param main A formula of the form (Forall x1,...,xN.A).
   * @param terms The list of terms with which to instantiate main. The caller of this
   * method has to ensure the correctness of these terms, and, specifically, that
   * A[x1\term1,...,xN\termN] indeed occurs at the bottom of the proof π.
   * @return A pair consisting of an LKProof and an SequentConnector.
   */
  def withSequentConnector( subProof: LKProof, main: Formula, terms: Seq[Expr] ): ( LKProof, SequentConnector ) = {
    val partiallyInstantiatedMains = ( 0 to terms.length ).toList.reverse.
      map( n => BetaReduction.betaNormalize( instantiate( main, terms.take( n ) ) ) )

    val series = terms.reverse.foldLeft(
      ( subProof, partiallyInstantiatedMains, SequentConnector( subProof.endSequent ) ) ) { ( acc, ai ) =>
        val newSubProof = ForallLeftRule( acc._1, acc._2.tail.head, ai )
        val newSequentConnector = newSubProof.getSequentConnector * acc._3
        ( newSubProof, acc._2.tail, newSequentConnector )
      }

    ( series._1, series._3 )
  }
}
