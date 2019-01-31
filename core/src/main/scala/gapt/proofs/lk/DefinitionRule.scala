package gapt.proofs.lk

import gapt.expr.Formula
import gapt.expr.Polarity
import gapt.proofs.IndexOrFormula
import gapt.proofs.SequentIndex

abstract class DefinitionRule extends UnaryLKProof with CommonRule {
  def subProof: LKProof
  def aux: SequentIndex
  def auxFormula: Formula = premise( aux )
  def mainFormula: Formula
}

object DefinitionRule extends ConvenienceConstructor( "DefinitionRule" ) {
  def apply( subProof: LKProof, aux: SequentIndex, main: Formula ): LKProof =
    apply( subProof, aux, main, aux.polarity )
  def apply( subProof: LKProof, aux: IndexOrFormula, main: Formula, polarity: Polarity ): LKProof =
    if ( polarity.inSuc )
      DefinitionRightRule( subProof, aux, main )
    else
      DefinitionLeftRule( subProof, aux, main )
}