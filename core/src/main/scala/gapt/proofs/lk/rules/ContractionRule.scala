package gapt.proofs.lk.rules

import gapt.expr.Formula
import gapt.proofs.SequentIndex

abstract class ContractionRule extends UnaryLKProof with CommonRule {
  def aux1: SequentIndex
  def aux2: SequentIndex

  override def auxIndices: Seq[Seq[SequentIndex]] = Seq( Seq( aux1, aux2 ) )

  val mainFormula: Formula = premise( aux1 )
}
