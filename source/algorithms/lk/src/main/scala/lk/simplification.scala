package at.logic.algorithms.lk

import scala.collection.immutable.Set
import at.logic.algorithms.subsumption.VariantsDeletion
import at.logic.calculi.lk.base.Sequent
import at.logic.language.hol.propositions._
import scala.collection.mutable.Map
import at.logic.language.lambda.typedLambdaCalculus.Var
import at.logic.algorithms.normalization.TermNormalizer

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

  object variantsRemoval {
    def apply(sequents: Set[Sequent]): Set[Sequent] = sequents.toList.foldLeft(Set[Sequent]())((ls, el) => if (ls.exists(x => isVariantSequent(x,el))) ls else (ls + el))
    private def isVariantSequent(s1: Sequent, s2: Sequent) = {
      val map = Map[Var,Var]();
      s1.antecedent.size == s2.antecedent.size && s1.succedent.size == s2.succedent.size &&
      s1.antecedent.zip(s2.antecedent).forall(x => VariantsDeletion.isVariantOf(x._1, x._2, map)) && s1.succedent.zip(s2.succedent).forall(x => VariantsDeletion.isVariantOf(x._1, x._2, map))
    }
  }

  // variable normalization and sorting according to a standard order, also removal of duplicates of formulas within the sequent
  object sequentNormalize {
    def apply(sequents: Set[Sequent]): Set[Sequent] = {
      sequents.toList.foldLeft(Set[Sequent]())((set, el) => {
          var id = 0
          val map = Map[Var,Var]()
          def nextId = {id = id + 1; id}
          set + (Sequent(normalize(el.antecedent,map,nextId),normalize(el.succedent,map,nextId)))
        })
    }
    private def normalize(ls: List[Formula], map: Map[Var,Var], nextId: => int): List[Formula] = toSet(ls.map(x => TermNormalizer(x,map,nextId).asInstanceOf[Formula]).sort((t1,t2) => t1.hashCode < t2.hashCode)).toList
    private def toSet[A](ls: List[A]): Set[A] = ls match {
      case x :: rest => toSet( rest ) + x
      case Nil => Set[A]()
    }
  }
}
