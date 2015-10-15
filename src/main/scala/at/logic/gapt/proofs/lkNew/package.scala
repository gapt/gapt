package at.logic.gapt.proofs

import at.logic.gapt.expr.HOLFormula

/**
 * Created by sebastian on 14.10.15.
 */
package object lkNew {
  implicit def LeftSequentIndex( i: SequentIndex ): Either[SequentIndex, HOLFormula] = Left( i )
  implicit def RightFormula( f: HOLFormula ): Either[SequentIndex, HOLFormula] = Right( f )
}
