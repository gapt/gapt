package at.logic.algorithms.lk

import scala.collection.immutable.Set
import at.logic.algorithms.subsumption.VariantsDeletion
import at.logic.calculi.lk.base.Sequent
import scala.collection.mutable.Map
import at.logic.language.lambda.typedLambdaCalculus.Var

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
    def apply(sequents: Set[Sequent]): Set[Sequent] = {val map = Map[Var,Var](); sequents.toList.foldLeft(Set[Sequent]())((ls, el) => if (ls.exists(x => isVariantSequent(x,el,map))) ls else (ls + el))}
    private def isVariantSequent(s1: Sequent, s2: Sequent, map: Map[Var,Var]) = s1.antecedent.size == s2.antecedent.size && s1.succedent.size == s2.succedent.size &&
      s1.antecedent.zip(s2.antecedent).forall(x => VariantsDeletion.isVariantOf(x._1, x._2, map)) && s1.succedent.zip(s2.succedent).forall(x => VariantsDeletion.isVariantOf(x._1, x._2, map))
  }
}
