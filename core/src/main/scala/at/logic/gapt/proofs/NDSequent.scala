package at.logic.gapt.proofs

import at.logic.gapt.expr.Polarity

/**
 * Sequents for natural deduction.
 *
 * They have the form A,,1,,,...,A,,m,, :- B (there is always exactly one element in the succedent).
 *
 * @param assumptions The elements A,,1,,,...,A,,m,,.
 * @param conclusion The element B.
 * @tparam A The type of elements in the sequent.
 */
case class NDSequent[+A]( assumptions: Seq[A], conclusion: A )

object NDSequent {

  def apply[A]( polarizedElements: Seq[( A, Polarity )] ): NDSequent[A] = {
    val ( ant, suc ) = polarizedElements.view.partition( _._2.inAnt )
    require( suc.size == 1 )
    NDSequent( ant.map( _._1 ), suc.head._1 )
  }

  /**
   * Implicit conversion to ordinary sequents.
   */
  implicit def toSequent[A]( s: NDSequent[A] ): Sequent[A] = Sequent( s.assumptions, Seq( s.conclusion ) )

}
