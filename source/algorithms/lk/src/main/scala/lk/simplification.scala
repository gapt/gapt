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
    def apply(sequents: List[Sequent]): List[Sequent] = sequents.toList.foldLeft(List[Sequent]())((ls, el) => if (ls.exists(x => isVariantSequent(x,el))) ls else (el::ls))
    private def isVariantSequent(s1: Sequent, s2: Sequent) = {
      val map = Map[Var,Var]();
      s1.antecedent.size == s2.antecedent.size && s1.succedent.size == s2.succedent.size &&
      s1.antecedent.zip(s2.antecedent).forall(x => VariantsDeletion.isVariantOf(x._1, x._2, map)) && s1.succedent.zip(s2.succedent).forall(x => VariantsDeletion.isVariantOf(x._1, x._2, map))
    }
  }

  // We first order the literals according to lexicographic order but ignoring the variables (as their names are unimportant)
  // Then we normalize the variables, remove duplicates and also normalize the return list by removing duplicates
  object sequentNormalize {
    def apply(sequents: List[Sequent]): List[Sequent] = {
      (sequents.foldLeft(List[Sequent]())((ls, el) => {
          var id = 0
          val map = Map[Var,Var]()
          def nextId = {id = id + 1; id}
          (Sequent(normalize(el.antecedent,map,nextId),normalize(el.succedent,map,nextId)))::ls
        })).removeDuplicates
    }
    private def normalize(ls: List[Formula], map: Map[Var,Var], nextId: => int): List[Formula] = 
      ls.sort((t1,t2) => myToString(t1) < myToString(t2)).map(x => TermNormalizer(x,map,nextId).asInstanceOf[Formula]).removeDuplicates
    private def myToString(exp: at.logic.language.lambda.typedLambdaCalculus.LambdaExpression): String = exp match {
      case v@ Var(at.logic.language.lambda.symbols.VariableStringSymbol(_),_) => ""
      case v: Var => v.toString
      case at.logic.language.lambda.typedLambdaCalculus.App(a,b) => myToString(a) + myToString(b)
      case at.logic.language.lambda.typedLambdaCalculus.Abs(a,b) => myToString(b)
    }
  }
}
