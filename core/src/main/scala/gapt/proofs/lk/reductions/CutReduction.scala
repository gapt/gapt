package gapt.proofs.lk.reductions

import gapt.proofs.lk.LKProof
import gapt.proofs.lk.rules.CutRule

trait CutReduction extends Reduction {
  def reduce(proof: LKProof): Option[LKProof] =
    proof match {
      case cut @ CutRule(_, _, _, _) => reduce(cut)
      case _                         => None
    }

  def reduce(proof: CutRule): Option[LKProof]

  def orElse(reduction: CutReduction): CutReduction =
    (cut: CutRule) => CutReduction.this.reduce(cut) orElse reduction.reduce(cut)

  def andThen(reduction: CutReduction): CutReduction =
    (cut: CutRule) => CutReduction.this.reduce(cut) flatMap reduction.reduce
}
