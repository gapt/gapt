package at.logic.algorithms.lk

import scala.collection.immutable.Set

import at.logic.calculi.lk.base.Sequent

object deleteTautologies
{
  def apply(sequents: List[Sequent]) : List[Sequent] =
    sequents.filter( s => s.antecedent.exists( f => s.succedent.contains( f ) ) )
}
