package gapt.proofs

import gapt.expr.{ ClosedUnderReplacement, Expr, containedNames }
import gapt.proofs.lk.rules.EqualityRule
import gapt.proofs.lk.rules.SkolemQuantifierRule

package object lk {
  implicit object LKProofSubstitutableDefault extends LKProofSubstitutable( false )

  implicit object lkProofReplaceable extends ClosedUnderReplacement[LKProof] {
    override def replace( proof: LKProof, p: PartialFunction[Expr, Expr] ): LKProof =
      new LKProofReplacer( p ).apply( proof, () )

    def names( proof: LKProof ) =
      proof.subProofs.flatMap {
        case p: EqualityRule         => containedNames( p.endSequent ) ++ containedNames( p.replacementContext )
        case p: SkolemQuantifierRule => containedNames( p.endSequent ) ++ containedNames( p.skolemTerm )
        case p                       => containedNames( p.endSequent )
      }
  }

  object normalizeLKt extends gapt.proofs.lkt.normalize
}