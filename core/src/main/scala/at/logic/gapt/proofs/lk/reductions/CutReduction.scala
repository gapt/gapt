package at.logic.gapt.proofs.lk.reductions

import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.lk.{CutRule, LKProof}

trait CutReduction extends Reduction {
  def reduce( proof: LKProof ): Option[LKProof] =
    proof match {
      case cut @ CutRule( _, _, _, _ ) => reduce( cut )
      case _                           => None
    }

  def reduce( proof: CutRule ): Option[LKProof]

  def orElse( reduction: CutReduction ): CutReduction =
    new CutReduction {
      def reduce( cut: CutRule ) =
        CutReduction.this.reduce( cut ) orElse reduction.reduce( cut )
    }

  def andThen( reduction: CutReduction ): CutReduction =
    new CutReduction {
      def reduce( cut: CutRule ) =
        CutReduction.this.reduce( cut ) flatMap reduction.reduce
    }
}