package at.logic.algorithms.lk

import scala.collection.immutable.Set

import at.logic.calculi.lk.base.Sequent

package simplification {

  object deleteTautologies
  {
    def apply(sequents: List[Sequent]) : List[Sequent] =
      sequents.filter( s => !s.antecedent.exists( f => s.succedent.contains( f ) ) )
  }

  object setNormalize
  {
    def apply(sequents: List[Sequent]) : Set[Sequent] = sequents match {
      case x :: rest => setNormalize( rest ) + x
      case Nil => Set[Sequent]()
    }
  }
}
