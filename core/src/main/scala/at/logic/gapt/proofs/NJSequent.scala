package at.logic.gapt.proofs

/**
 * Sequents for the intuitionistic calculus NJ, i.e. natural deduction with sequents.
 *
 * They have the form A,,1,,,...,A,,m,, :- B (there is always exactly one element in the succedent).
 * @param assumptions The elements A,,1,,,...,A,,m,,.
 * @param conclusion The element B.
 * @tparam A The type of elements in the sequent.
 */
case class NJSequent[+A]( assumptions: Seq[A], conclusion: A )

object NJSequent {
  /**
   * Implicit conversion to ordinary sequents.
   */
  implicit def toSequent[A]( s: NJSequent[A] ): Sequent[A] = Sequent( s.assumptions, Seq( s.conclusion ) )
}
