package gapt.proofs.lk.reductions

import gapt.proofs.context.Context
import gapt.proofs.lk.LKProof

trait Reduction {

  def reduce( proof: LKProof ): Option[LKProof]

  def orElse( reduction: Reduction ): Reduction =
    new Reduction {
      def reduce( proof: LKProof ): Option[LKProof] =
        Reduction.this.reduce( proof ) orElse reduction.reduce( proof )
    }

  def andThen( reduction: Reduction ): Reduction =
    new Reduction {
      def reduce( proof: LKProof ): Option[LKProof] =
        Reduction.this.reduce( proof ) flatMap reduction.reduce
    }

  def isRedex( proof: LKProof ): Boolean =
    reduce( proof ).nonEmpty

  def redexes( proof: LKProof ): Seq[LKProof] =
    proof.subProofs.filter { isRedex( _ ) }.toSeq
}