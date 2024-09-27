package gapt.proofs

import gapt.logic.Polarity

/**
 * Sequents for natural deduction.
 *
 * They have the form A,,1,,,...,A,,m,, :- B (there is always exactly one element in the succedent).
 *
 * @param assumptions The elements A,,1,,,...,A,,m,,.
 * @param conclusion The element B.
 * @tparam A The type of elements in the sequent.
 */
case class NDSequent[+A](assumptions: Seq[A], conclusion: A) {
  def :-[B >: A](newConclusion: B): NDSequent[B] =
    copy(conclusion = newConclusion)

  def +:[B >: A](additionalAssumption: B): NDSequent[B] =
    copy(assumptions = additionalAssumption +: assumptions)

  def ++:[B >: A](additionalAssumptions: Iterable[B]): NDSequent[B] =
    copy(assumptions = additionalAssumptions ++: assumptions)
}

object NDSequent {

  def apply[A](polarizedElements: Seq[(A, Polarity)]): NDSequent[A] = {
    val (ant, suc) = polarizedElements.view.partition(_._2.inAnt)
    require(suc.size == 1)
    NDSequent(ant.map(_._1).toSeq, suc.head._1)
  }

  /**
   * Implicit conversion to ordinary sequents.
   */
  implicit def toSequent[A](s: NDSequent[A]): Sequent[A] = Sequent(s.assumptions, Seq(s.conclusion))

}
