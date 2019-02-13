package gapt.proofs.lk.rules.macros

import gapt.expr.Formula
import gapt.expr.Var
import gapt.expr.hol.instantiate
import gapt.proofs.SequentConnector
import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.ExistsLeftRule

object ExistsLeftBlock {
  /**
   * Applies the ExistsLeft-rule n times.
   * This method expects a formula main with
   * a quantifier block, and a proof s1 which has a fully
   * instantiated version of main on the left side of its
   * bottommost sequent.
   *
   * The rule:
   * <pre>
   *              (π)
   *    A[x1\y1,...,xN\yN], Γ :- Δ
   * ---------------------------------- (∀_r x n)
   *     ∃x1,..,xN.A, Γ :- Δ
   *
   * where y1,...,yN are eigenvariables.
   * </pre>
   *
   * @param subProof The proof π with (A[x1\y1,...,xN\yN], Γ :- Δ) as the bottommost sequent.
   * @param main A formula of the form (∃ x1,...,xN.A).
   * @param eigenvariables The list of eigenvariables with which to instantiate main. The caller of this
   * method has to ensure the correctness of these terms, and, specifically, that
   * A[x1\y1,...,xN\yN] indeed occurs at the bottom of the proof π.
   */
  def apply( subProof: LKProof, main: Formula, eigenvariables: Seq[Var] ): LKProof =
    withSequentConnector( subProof, main, eigenvariables )._1

  /**
   * Applies the ExistsLeft-rule n times.
   * This method expects a formula main with
   * a quantifier block, and a proof s1 which has a fully
   * instantiated version of main on the left side of its
   * bottommost sequent.
   *
   * The rule:
   * <pre>
   *              (π)
   *    A[x1\y1,...,xN\yN], Γ :- Δ
   * ---------------------------------- (∀_r x n)
   *     ∃x1,..,xN.A, Γ :- Δ
   *
   * where y1,...,yN are eigenvariables.
   * </pre>
   *
   * @param subProof The proof π with (A[x1\y1,...,xN\yN], Γ :- Δ) as the bottommost sequent.
   * @param main A formula of the form (∃ x1,...,xN.A).
   * @param eigenvariables The list of eigenvariables with which to instantiate main. The caller of this
   * method has to ensure the correctness of these terms, and, specifically, that
   * A[x1\y1,...,xN\yN] indeed occurs at the bottom of the proof π.
   * @return A pair consisting of an LKProof and an SequentConnector.
   */
  def withSequentConnector( subProof: LKProof, main: Formula,
                            eigenvariables: Seq[Var] ): ( LKProof, SequentConnector ) = {
    val partiallyInstantiatedMains = ( 0 to eigenvariables.length ).toList.reverse.
      map( n => instantiate( main, eigenvariables.take( n ) ) )

    val series = eigenvariables.reverse.foldLeft(
      ( subProof, partiallyInstantiatedMains, SequentConnector( subProof.endSequent ) ) ) { ( acc, ai ) =>
        val newSubProof = ExistsLeftRule( acc._1, acc._2.tail.head, ai )
        val newSequentConnector = newSubProof.getSequentConnector * acc._3
        ( newSubProof, acc._2.tail, newSequentConnector )
      }

    ( series._1, series._3 )
  }
}
