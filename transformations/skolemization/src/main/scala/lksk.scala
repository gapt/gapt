// This package implements the higher-order analogue to Skolemization:
// a transformation from LK to LK_skc
package at.logic.transformations.skolemization.lksk

import scala.collection.mutable.{Map,HashMap}
import at.logic.calculi.lksk._
import at.logic.calculi.lksk.base._
import at.logic.calculi.lksk.base.TypeSynonyms._
import at.logic.calculi.lk.propositionalRules.{Axiom => LKAxiom}
import at.logic.calculi.occurrences._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.base.{LKProof,Sequent}

object LKtoLKskc {
  def apply(proof: LKProof) = {
    // initialize map from occurrences to substitution terms:
    // in the end-sequent, there are no substitution terms for any
    // formula occurrences on the path to the end-sequent
    val subst_terms = new HashMap[FormulaOccurrence, Label]
    proof.root.antecedent.foreach( fo => subst_terms.update( fo, EmptyLabel() ) )
    proof.root.succedent.foreach( fo => subst_terms.update( fo, EmptyLabel() ) )
    rec( proof, subst_terms )._1
  }
  
  def rec(proof: LKProof, subst_terms: Map[FormulaOccurrence, Label]) : (LKProof, Map[FormulaOccurrence,LabelledFormulaOccurrence]) = proof match {
    case LKAxiom(so) => {
      val ant = so.antecedent.toList
      val succ = so.succedent.toList
      val a = Axiom( Sequent( ant.map( fo => fo.formula ), succ.map( fo => fo.formula ) ),
                     Pair( ant.map( fo => subst_terms.apply( fo ) ), 
                           succ.map( fo => subst_terms.apply( fo ) ) ) )
      val map = new HashMap[FormulaOccurrence, LabelledFormulaOccurrence]
      a._2._1.zip(a._2._1.indices).foreach( p => map.update( ant( p._2 ), p._1 ) )
      a._2._2.zip(a._2._2.indices).foreach( p => map.update( ant( p._2 ), p._1 ) )
      (a._1, map)
    }
    case ForallLeftRule(p, s, a, m, t) => {
      val new_label_map = contextMap( (s.antecedent - m) ++ s.succedent, subst_terms ) + Pair(a, subst_terms(m) + t)
      val r = rec( p, new_label_map )
      val sk_proof = ForallSkLeftRule( r._1, r._2(a), m.formula, t, !subst_terms(m).contains(t) )
      val map = new HashMap[FormulaOccurrence, LabelledFormulaOccurrence]
      p.root.antecedent.foreach( fo => map.update( proof.getDescendantInLowerSequent( fo ).get, 
        sk_proof.getDescendantInLowerSequent( r._2(fo) ).get.asInstanceOf[LabelledFormulaOccurrence] ) )
      (sk_proof, map)
    }
  }

  def contextMap( fos: Set[FormulaOccurrence], map: Map[FormulaOccurrence, Label] ) : 
    Map[FormulaOccurrence, Label] = map ++ fos.map( fo => Pair(fo.ancestors.first, map( fo ) ) )
}
