package at.logic.algorithms.lk

import scala.collection.immutable.Set
import at.logic.algorithms.subsumption.VariantsDeletion
import at.logic.calculi.lk.base.Sequent
import at.logic.language.hol._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.symbols._
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
    def apply(sequents: List[Sequent]): List[Sequent] = sequents.foldLeft(List[Sequent]())((ls, el) => if (ls.exists(x => isVariantSequent(x,el))) ls else (el::ls))
    private def isVariantSequent(s1: Sequent, s2: Sequent) = {
      val map = Map[Var,Var]();
      s1.antecedent.size == s2.antecedent.size && s1.succedent.size == s2.succedent.size &&
      s1.antecedent.zip(s2.antecedent).forall(x => VariantsDeletion.isVariantOf(x._1, x._2, map)) && s1.succedent.zip(s2.succedent).forall(x => VariantsDeletion.isVariantOf(x._1, x._2, map))
    }
  }
  
  object subsumedClausesRemovalHOL {
    val alg = new at.logic.algorithms.subsumption.StillmanSubsumptionAlgorithm {val matchAlg = at.logic.algorithms.matching.hol.NaiveIncompleteMatchingAlgorithm}
    def apply(sequents: List[Sequent]): List[Sequent] = sequents.foldLeft(List[Sequent]())((ls, el) => forward(el, backward(el, ls)))
    private def forward(el: Sequent, ls: List[Sequent]) = if (ls.exists(x => alg.subsumes(x, el))) ls else (el::ls)
    private def backward(el: Sequent, ls: List[Sequent]) = ls.remove(x => alg.subsumes(el, x))
  }
  object subsumedClausesRemoval {
    val alg = new at.logic.algorithms.subsumption.StillmanSubsumptionAlgorithm {val matchAlg = at.logic.algorithms.matching.fol.FOLMatchingAlgorithm}
    def apply(sequents: List[Sequent]): List[Sequent] = sequents.foldLeft(List[Sequent]())((ls, el) => forward(el, backward(el, ls)))
    private def forward(el: Sequent, ls: List[Sequent]) = if (ls.exists(x => alg.subsumes(x, el))) ls else (el::ls)
    private def backward(el: Sequent, ls: List[Sequent]) = ls.remove(x => alg.subsumes(el, x))
  }

  // for any positive unit clause, we try to match it with all negative "ground" literals of the other clauses, if there is a match we remove the literal.
  object simpleUnitResolutionNormalization {
    val alg = at.logic.algorithms.matching.hol.NaiveIncompleteMatchingAlgorithm
    def apply(seqs: List[Sequent]): List[Sequent] = {
      val posUnit = seqs.filter(x => x.antecedent.isEmpty && x.succedent.size == 1)
      seqs.map(x => if (!x.antecedent.isEmpty) (matchPos(posUnit, x)) else x)
    }
    private def matchPos(posUnit: List[Sequent], s: Sequent): Sequent = {
      val newAnt = s.antecedent.filter(x => posUnit.forall(y => alg.matchTerm(y.succedent.head, x) == None))
      if (newAnt.size == s.antecedent.size) s else Sequent(newAnt, s.succedent)
    }
    // no need to check for groundness as the matching algorithm does not return a substitution which can affect the instance
    /*// should be moved into HOLTerm when we have one
    private def isGround(exp: LambdaExpression): Boolean = exp match {
      case v @ Var(VariableStringSymbol(_),_) if v.asInstanceOf[Var].isFree => false
      case Var(_,_) => true
      case App(a,b) => isGround(a) && isGround(b)
      case AbsInScope(_,a) => isGround(a)
    }*/
  }
  // We first order the literals according to lexicographic order but ignoring the variables (as their names are unimportant)
  // Then we normalize the variables, remove duplicates and also normalize the return list by removing duplicates
  object sequentNormalize {
    def apply(sequents: List[Sequent]): List[Sequent] = {
      (sequents.foldLeft(List[Sequent]())((ls, el) => {
          var id = 0
          val map = Map[Var,Var]()
          def nextId = {id = id + 1; id}
          (Sequent(normalize(el.antecedent,map,nextId).asInstanceOf[List[HOLFormula]],normalize(el.succedent,map,nextId).asInstanceOf[List[HOLFormula]]))::ls
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
