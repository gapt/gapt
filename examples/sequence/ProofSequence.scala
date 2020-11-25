package gapt.examples.sequence

import gapt.proofs.lk.LKProof

trait ProofSequence {
  def apply( n: Int ): LKProof

  def name = getClass.getSimpleName.replace( "$", "" )
}
