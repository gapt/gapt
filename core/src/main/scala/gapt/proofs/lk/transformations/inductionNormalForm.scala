package gapt.proofs.lk.transformations

import gapt.proofs.context.Context
import gapt.proofs.lk.LKProof

object inductionNormalForm {
  /**
   * Transforms a proof to a proof without "unnecessary" induction inferences.
   *
   * @param proof The proof to which the transformation is applied.
   * @param ctx The context with respect to which this proof transformation is computed.
   * @return A proof obtained by repeated cut normalization and induction unfolding. The resulting proof does
   *         not contain inductions that can be unfolded.
   */
  def apply( proof: LKProof )( implicit ctx: Context ): LKProof = {
    var newProof = proof
    var continue = false
    do {
      continue = false
      newProof = pushEqualityInferencesToLeaves( newProof )
      newProof = cutNormal( newProof )
      val inductionUnfolder = new UnfoldInductions
      newProof = inductionUnfolder( newProof )
      continue = inductionUnfolder.unfoldedInduction
    } while ( continue )
    newProof
  }
}
