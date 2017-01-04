package at.logic.gapt.proofs

import at.logic.gapt.expr.{ ClosedUnderReplacement, HOLFormula, LambdaExpression, containedNames }

package object lk {
  implicit def LeftSequentIndex( i: SequentIndex ): Either[SequentIndex, HOLFormula] = Left( i )
  implicit def RightFormula( f: HOLFormula ): Either[SequentIndex, HOLFormula] = Right( f )

  implicit object LKProofSubstitutableDefault extends LKProofSubstitutable( false )

  implicit object lkProofReplaceable extends ClosedUnderReplacement[LKProof] {
    override def replace( proof: LKProof, p: PartialFunction[LambdaExpression, LambdaExpression] ): LKProof =
      new LKProofReplacer( p ).apply( proof, () )

    def names( proof: LKProof ) =
      proof.subProofs.flatMap {
        case p: EqualityRule         => containedNames( p.endSequent ) ++ containedNames( p.replacementContext )
        case p: SkolemQuantifierRule => containedNames( p.endSequent ) ++ containedNames( p.skolemTerm ) ++ containedNames( p.skolemDef )
        case p                       => containedNames( p.endSequent )
      }
  }
}