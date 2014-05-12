
package at.logic.algorithms.lk

import at.logic.algorithms.subsumption._
import at.logic.algorithms.matching._
import at.logic.calculi.lk.base.FSequent
import at.logic.language.hol._

object deleteTautologies
{
  def apply(sequents: List[FSequent]) : List[FSequent] =
    sequents.filter( s => !s._1.exists( f => s._2.contains( f ) ) )
}

object setNormalize
{
  def apply(sequents: List[FSequent]) : Set[FSequent] = sequents match {
    case x :: rest => setNormalize( rest ) + x
    case Nil => Set[FSequent]()
  }
}

object subsumedClausesRemovalHOL {
  val alg = StillmanSubsumptionAlgorithmHOL
  def apply(sequents: List[FSequent]): List[FSequent] = sequents.foldLeft(List[FSequent]())((ls, el) => forward(el, backward(el, ls)))
  private def forward(el: FSequent, ls: List[FSequent]) = if (ls.exists(x => alg.subsumes(x, el))) ls else (el::ls)
  private def backward(el: FSequent, ls: List[FSequent]) = ls.filterNot(x => alg.subsumes(el, x))
}
object subsumedClausesRemoval {
  val alg = StillmanSubsumptionAlgorithmFOL
  def apply(sequents: List[FSequent]): List[FSequent] = sequents.foldLeft(List[FSequent]())((ls, el) => forward(el, backward(el, ls)))
  private def forward(el: FSequent, ls: List[FSequent]) = if (ls.exists(x => alg.subsumes(x, el))) ls else (el::ls)
  private def backward(el: FSequent, ls: List[FSequent]) = ls.filterNot(x => alg.subsumes(el, x))
}

// for any positive unit clause, we try to match it with all negative "ground" literals of the other clauses, if there is a match we remove the literal.
object simpleUnitResolutionNormalization {
  val alg = NaiveIncompleteMatchingAlgorithm
  def apply(seqs: List[FSequent]): List[FSequent] = {
    val posUnit = seqs.filter(x => x._1.isEmpty && x._2.size == 1)
    seqs.map(x => if (!x._1.isEmpty) (matchPos(posUnit, x)) else x)
  }
  private def matchPos(posUnit: List[FSequent], s: FSequent): FSequent = {
    val restDomain = (s._1.flatMap(x => freeVariables(x)) ++ s._2.flatMap(x => freeVariables(x))).toList
    val newAnt = s._1.filter(x => posUnit.forall(y => alg.matchTerm(y._2.head, x, restDomain) == None))
    if (newAnt.size == s._1.size) s else new FSequent(newAnt, s._2)
  }
}


