package at.logic.gapt.proofs

import at.logic.gapt.expr.{ ClosedUnderReplacement, HOLFormula, LambdaExpression }

/**
 * Created by sebastian on 14.10.15.
 */
package object lk {
  implicit def LeftSequentIndex( i: SequentIndex ): Either[SequentIndex, HOLFormula] = Left( i )
  implicit def RightFormula( f: HOLFormula ): Either[SequentIndex, HOLFormula] = Right( f )

  implicit object LKProofSubstitutableDefault extends LKProofSubstitutable( false )

  implicit object lkProofReplaceable extends ClosedUnderReplacement[LKProof] {
    override def replace( proof: LKProof, p: PartialFunction[LambdaExpression, LambdaExpression] ): LKProof =
      new LKProofReplacer( p ).apply( proof, () )
  }
}