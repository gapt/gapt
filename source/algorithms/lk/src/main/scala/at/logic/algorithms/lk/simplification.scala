package at.logic.algorithms.lk

import at.logic.algorithms.subsumption.VariantsDeletion
import at.logic.calculi.lk.base.Sequent
import at.logic.language.hol._
import at.logic.language.lambda.typedLambdaCalculus._
import at.logic.language.lambda.symbols._
import scala.collection.mutable.Map
import at.logic.language.lambda.typedLambdaCalculus.Var
import at.logic.calculi.occurrences._
import at.logic.calculi.lk.base.types._

package simplification {

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

  object variantsRemoval {
    def apply(sequents: List[FSequent]): List[FSequent] = sequents.foldLeft(List[FSequent]())((ls, el) => if (ls.exists(x => isVariantSequent(x,el))) ls else (el::ls))
    private def isVariantSequent(s1: FSequent, s2: FSequent) = {
      val map = Map[Var,Var]();
      s1._1.size == s2._1.size && s1._2.size == s2._2.size &&
      s1._1.zip(s2._1).forall(x => VariantsDeletion.isVariantOf(x._1, x._2, map)) && s1._2.zip(s2._2).forall(x => VariantsDeletion.isVariantOf(x._1, x._2, map))
    }
  }
  
  object subsumedClausesRemovalHOL {
    val alg = new at.logic.algorithms.subsumption.StillmanSubsumptionAlgorithm[HOLExpression] {val matchAlg = at.logic.algorithms.matching.hol.NaiveIncompleteMatchingAlgorithm}
    def apply(sequents: List[FSequent]): List[FSequent] = sequents.foldLeft(List[FSequent]())((ls, el) => forward(el, backward(el, ls)))
    private def forward(el: FSequent, ls: List[FSequent]) = if (ls.exists(x => alg.subsumes(x, el))) ls else (el::ls)
    private def backward(el: FSequent, ls: List[FSequent]) = ls.filterNot(x => alg.subsumes(el, x))
  }
  object subsumedClausesRemoval {
    val alg = new at.logic.algorithms.subsumption.StillmanSubsumptionAlgorithm[at.logic.language.fol.FOLExpression] {val matchAlg = at.logic.algorithms.matching.fol.FOLMatchingAlgorithm}
    def apply(sequents: List[FSequent]): List[FSequent] = sequents.foldLeft(List[FSequent]())((ls, el) => forward(el, backward(el, ls)))
    private def forward(el: FSequent, ls: List[FSequent]) = if (ls.exists(x => alg.subsumes(x, el))) ls else (el::ls)
    private def backward(el: FSequent, ls: List[FSequent]) = ls.filterNot(x => alg.subsumes(el, x))
  }

  // for any positive unit clause, we try to match it with all negative "ground" literals of the other clauses, if there is a match we remove the literal.
  object simpleUnitResolutionNormalization {
    val alg = at.logic.algorithms.matching.hol.NaiveIncompleteMatchingAlgorithm
    def apply(seqs: List[FSequent]): List[FSequent] = {
      val posUnit = seqs.filter(x => x._1.isEmpty && x._2.size == 1)
      seqs.map(x => if (!x._1.isEmpty) (matchPos(posUnit, x)) else x)
    }
    private def matchPos(posUnit: List[FSequent], s: FSequent): FSequent = {
      val restDomain = (s._1.flatMap(x => x.freeVariables) ++ s._2.flatMap(x => x.freeVariables)).toList
      val newAnt = s._1.filter(x => posUnit.forall(y => alg.matchTerm(y._2.head, x, restDomain) == None))
      if (newAnt.size == s._1.size) s else new FSequent(newAnt, s._2)
    }
    // no need to check for groundness as the matching algorithm does not return a substitution which can affect the instance
    /*// should be moved into HOLExpression when we have one
    private def isGround(exp: LambdaExpression): Boolean = exp match {
      case v @ Var(VariableStringSymbol(_),_) if v.asInstanceOf[Var].isFree => false
      case Var(_,_) => true
      case App(a,b) => isGround(a) && isGround(b)
      case Abs(_,a) => isGround(a)
    }*/
  }
  // We first order the literals according to lexicographic order but ignoring the variables (as their names are unimportant)
  // Then we normalize the variables, remove duplicates and also normalize the return list by removing duplicates
  object sequentNormalize {
    def apply(sequents: List[FSequent]): List[FSequent] = {
      (sequents.foldLeft(List[FSequent]())((ls, el) => {
          var id = 0
          //def nextId = {id = id + 1; id}
          val antecedent = normalize(el._1,0)
          val succedent = normalize(el._2,0)
          val newfs = new FSequent(antecedent, succedent)
          println(newfs)

          (newfs::ls)
        })).distinct
    }
    //TODO: add blacklist to normalization (symbols contained in formula may not be reused)
    private def normalize(ls: Seq[HOLFormula], startId : Int): Seq[HOLFormula] =
      ls.sortWith((t1,t2) => myToString(t1) < myToString(t2)).map(x => (Normalization(x, startId, "x")._1).asInstanceOf[HOLFormula]).distinct
    private def myToString(exp: at.logic.language.lambda.typedLambdaCalculus.LambdaExpression): String = exp match {
      case v@ Var(at.logic.language.lambda.symbols.VariableStringSymbol(_),_) => ""
      case v: Var => v.toString
      case at.logic.language.lambda.typedLambdaCalculus.App(a,b) => myToString(a) + myToString(b)
      case at.logic.language.lambda.typedLambdaCalculus.Abs(a,b) => myToString(b)
    }
  }
}
