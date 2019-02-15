package gapt.proofs.lk.rules

import gapt.expr.Abs
import gapt.expr.App
import gapt.expr.BetaReduction
import gapt.expr.formula.Eq
import gapt.expr.formula.Formula
import gapt.proofs.Ant
import gapt.proofs.SequentIndex
import gapt.proofs.Suc
import gapt.proofs.lk.LKProof

/**
 * Abstract class that performs most of the construction of left and right equality rules.
 */
abstract class EqualityRule extends UnaryLKProof with CommonRule {

  def subProof: LKProof
  def eq: SequentIndex
  def aux: SequentIndex
  def replacementContext: Abs

  aux match {
    case Ant( _ ) => validateIndices( premise, Seq( eq, aux ), Seq() )
    case Suc( _ ) => validateIndices( premise, Seq( eq ), Seq( aux ) )
  }

  def equation: Formula = premise( eq )

  val auxFormula: Formula = premise( aux )

  val ( what, by, leftToRight ) = equation match {
    case Eq( s, t ) =>
      val insertS = BetaReduction.betaNormalize( App( replacementContext, s ) )
      val insertT = BetaReduction.betaNormalize( App( replacementContext, t ) )
      if ( insertS == auxFormula ) {
        ( s, t, true )
      } else if ( insertT == auxFormula ) {
        ( t, s, false )
      } else {
        throw LKRuleCreationException( s"Inserting $s into context yields $insertS; inserting" +
          s" $t yields $insertT. Neither is equal to $auxFormula." )
      }
    case _ => throw LKRuleCreationException( s"Formula $equation is not an equation." )
  }

  def mainFormula: Formula = BetaReduction.betaNormalize( App( replacementContext, by ) ).asInstanceOf[Formula]

  def auxIndices: Seq[Seq[SequentIndex]] = Seq( Seq( eq, aux ) )

  override def formulasToBeDeleted: Seq[Seq[SequentIndex]] = Seq( Seq( aux ) )

  def auxInConclusion: SequentIndex = mainIndices.head
  def eqInConclusion: SequentIndex = getSequentConnector.child( eq )

}
