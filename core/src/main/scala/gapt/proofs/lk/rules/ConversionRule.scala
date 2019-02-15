package gapt.proofs.lk.rules

import gapt.expr.Polarity
import gapt.expr.formula.Formula
import gapt.proofs.IndexOrFormula
import gapt.proofs.SequentIndex
import gapt.proofs.lk.LKProof

abstract class ConversionRule extends UnaryLKProof with CommonRule {
  def subProof: LKProof
  def aux: SequentIndex
  def auxFormula: Formula = premise( aux )
  def mainFormula: Formula
}

object ConversionRule extends ConvenienceConstructor( "ConversionRule" ) {
  def apply( subProof: LKProof, aux: SequentIndex, main: Formula ): LKProof =
    apply( subProof, aux, main, aux.polarity )
  def apply( subProof: LKProof, aux: IndexOrFormula, main: Formula, polarity: Polarity ): LKProof =
    if ( polarity.inSuc )
      ConversionRightRule( subProof, aux, main )
    else
      ConversionLeftRule( subProof, aux, main )
}