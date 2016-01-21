package at.logic.gapt.proofs

import at.logic.gapt.expr.{ Substitution, Substitutable, HOLFormula }

/**
 * Created by sebastian on 14.10.15.
 */
package object lk {
  implicit def LeftSequentIndex( i: SequentIndex ): Either[SequentIndex, HOLFormula] = Left( i )
  implicit def RightFormula( f: HOLFormula ): Either[SequentIndex, HOLFormula] = Right( f )

  implicit object LKProofSubstitutableDefault extends LKProofSubstitutable( false )
}