package at.logic.algorithms.lksk

import scala.collection.mutable.{Map, HashMap}

import at.logic.calculi.lksk._
import at.logic.calculi.lksk.base._
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.lkExtractors.{UnaryLKProof, BinaryLKProof}
import at.logic.language.hol.substitutions.Substitution
import at.logic.language.hol.propositions._
import at.logic.algorithms.lk.{applySubstitution => LKapplySubstitution}

object applySubstitution {

  def toLabelledSequentOccurrence( so: SequentOccurrence )
    = new LabelledSequentOccurrence( so.antecedent.map( fo => fo.asInstanceOf[LabelledFormulaOccurrence] ),
                                     so.succedent.map( fo => fo.asInstanceOf[LabelledFormulaOccurrence] ) )

def apply( proof: LKProof, subst: Substitution ) : (LKProof, Map[LabelledFormulaOccurrence, LabelledFormulaOccurrence]) =
  proof match {
    case Axiom(so : LabelledSequentOccurrence) => {
      val ant_occs  = so.l_antecedent.toList
      val succ_occs = so.l_succedent.toList
      val a = Axiom(Sequent(ant_occs.map( fo => subst(fo.formula) ), succ_occs.map( fo => subst(fo.formula) ) ),
        Pair( ant_occs.map( fo => fo.label.map( t => subst.applyHOL(t) ) ), 
              succ_occs.map( fo => fo.label.map( t => subst.applyHOL(t) ) ) ) )
      val map = new HashMap[LabelledFormulaOccurrence, LabelledFormulaOccurrence]
      a._2._1.zip(a._2._1.indices).foreach( p => map.update( ant_occs( p._2 ), p._1 ) )
      a._2._2.zip(a._2._2.indices).foreach( p => map.update( succ_occs( p._2 ), p._1 ) )
      (a._1, map)
    }
    case WeakeningLeftRule(p, s, m) => {
      val new_parent = apply( p, subst )
      val new_proof = WeakeningLeftRule( new_parent._1, subst(m.formula), m.label.map( e => subst.applyHOL(e) ) )
      val es = toLabelledSequentOccurrence( p.root )
      ( new_proof, computeMap( es.l_antecedent ++ es.l_succedent, proof, new_proof, new_parent._2 ) + Pair(m, new_proof.prin.first ) )
    }
    case WeakeningRightRule(p, s, m) => {
      val new_parent = apply( p, subst )
      val new_proof = WeakeningRightRule( new_parent._1, subst(m.formula), m.label.map( e => subst.applyHOL(e) ) )
      val es = toLabelledSequentOccurrence( p.root )
      ( new_proof, computeMap( es.l_antecedent ++ es.l_succedent, proof, new_proof, new_parent._2 ) + Pair(m, new_proof.prin.first ) )
    }
    case ForallSkLeftRule(p, s, a, m, t) => {
      val new_parent = apply( p, subst )
      val new_proof = ForallSkLeftRule( new_parent._1, new_parent._2(a), subst(m.formula), subst.applyHOL(t), a.label.contains(t) )
      val es = toLabelledSequentOccurrence( p.root )
      ( new_proof, computeMap( es.l_antecedent ++ es.l_succedent, proof, new_proof, new_parent._2 ) )
    }
    case ExistsSkRightRule(p, s, a, m, t) => {
      val new_parent = apply( p, subst )
      val new_proof = ExistsSkRightRule( new_parent._1, new_parent._2(a), subst(m.formula), subst.applyHOL(t), a.label.contains(t) )
      val es = toLabelledSequentOccurrence( p.root )
      ( new_proof, computeMap( es.l_antecedent ++ es.l_succedent, proof, new_proof, new_parent._2 ) )
    }
    case ForallSkRightRule(p, s, a, m, t) => {
      val new_parent = apply( p, subst )
      val new_proof = ForallSkRightRule( new_parent._1, new_parent._2(a), subst(m.formula), subst.applyHOL( t ) )
      val es = toLabelledSequentOccurrence( p.root )
      ( new_proof, computeMap( es.l_antecedent ++ es.l_succedent, proof, new_proof, new_parent._2 ) )
    }
    case ExistsSkLeftRule(p, s, a, m, t) => {
      val new_parent = apply( p, subst )
      val new_proof = ExistsSkLeftRule( new_parent._1, new_parent._2(a), subst(m.formula), subst.applyHOL( t ) )
      val es = toLabelledSequentOccurrence( p.root )
      ( new_proof, computeMap( es.l_antecedent ++ es.l_succedent, proof, new_proof, new_parent._2 ) )
    }
    // casts should not be necessary!
    // Map[LabelledFormulaOccurrence,LabelledFormulaOccurrence] is a Map[FormulaOccurrence, FormulaOccurrence]
    // is Map not covariant, like set?
    case UnaryLKProof(_, p, _, _, _) => LKapplySubstitution.handleRule( proof, 
      apply( p, subst ).asInstanceOf[(LKProof, Map[FormulaOccurrence,FormulaOccurrence])]::Nil, subst ).asInstanceOf[(LKProof, Map[LabelledFormulaOccurrence, LabelledFormulaOccurrence])]
    case BinaryLKProof(_, p1, p2, _, _, _, _) =>
      LKapplySubstitution.handleRule( proof, (apply( p1, subst )::apply( p2, subst )::Nil).asInstanceOf[List[(LKProof, Map[FormulaOccurrence,FormulaOccurrence])]], subst ).asInstanceOf[(LKProof, Map[LabelledFormulaOccurrence, LabelledFormulaOccurrence])]
  }

  // TODO: a very similar method is used in LKtoLKskc, refactor!?
  def computeMap( occs: Set[LabelledFormulaOccurrence], old_proof: LKProof, 
                  new_proof: LKProof, old_map : Map[LabelledFormulaOccurrence, LabelledFormulaOccurrence]) =
  {
    val map = new HashMap[LabelledFormulaOccurrence, LabelledFormulaOccurrence]
    occs.foreach( fo => map.update( old_proof.getDescendantInLowerSequent( fo ).get.asInstanceOf[LabelledFormulaOccurrence], 
      new_proof.getDescendantInLowerSequent( old_map(fo) ).get.asInstanceOf[LabelledFormulaOccurrence] ) )
    map
  }
}
