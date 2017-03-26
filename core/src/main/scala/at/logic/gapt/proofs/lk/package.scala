package at.logic.gapt.proofs

import at.logic.gapt.expr.{ ClosedUnderReplacement, Formula, Expr, containedNames }

package object lk {
  implicit def LeftSequentIndex( i: SequentIndex ): Either[SequentIndex, Formula] = Left( i )
  implicit def RightFormula( f: Formula ): Either[SequentIndex, Formula] = Right( f )

  implicit object LKProofSubstitutableDefault extends LKProofSubstitutable( false )

  implicit object lkProofReplaceable extends ClosedUnderReplacement[LKProof] {
    override def replace( proof: LKProof, p: PartialFunction[Expr, Expr] ): LKProof =
      new LKProofReplacer( p ).apply( proof, () )

    def names( proof: LKProof ) =
      proof.subProofs.flatMap {
        case p: EqualityRule         => containedNames( p.endSequent ) ++ containedNames( p.replacementContext )
        case p: SkolemQuantifierRule => containedNames( p.endSequent ) ++ containedNames( p.skolemTerm ) ++ containedNames( p.skolemDef )
        case p                       => containedNames( p.endSequent )
      }
  }
}