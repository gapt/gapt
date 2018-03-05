package at.logic.gapt.proofs.lk.reductions

import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.lk.{CutRule, LKProof}

trait Reduction {

  def reduce( proof: LKProof )( implicit ctx: Context ): Option[LKProof]

  def orElse( reduction: Reduction ): Reduction =
    new Reduction {
      def reduce( proof: LKProof )( implicit ctx: Context ) =
        Reduction.this.reduce( proof ) orElse reduction.reduce( proof )
    }

  def andThen( reduction: Reduction ): Reduction =
    new Reduction {
      def reduce( proof: LKProof )( implicit ctx: Context ) =
        Reduction.this.reduce( proof ) flatMap reduction.reduce
    }

  def isRedex( proof: LKProof )( implicit ctx: Context ): Boolean =
    reduce( proof ).nonEmpty

  def redexes( proof: LKProof )( implicit ctx: Context ): Seq[LKProof] =
    proof.subProofs.filter { isRedex( _ ) }.toSeq
}