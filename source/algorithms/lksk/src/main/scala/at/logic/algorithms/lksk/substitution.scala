package at.logic.algorithms.lksk

import at.logic.calculi.lksk._
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.{UnaryLKProof, BinaryLKProof}
import at.logic.language.hol._
import at.logic.algorithms.lk.{applySubstitution => LKapplySubstitution, ProofTransformationUtils}

object applySubstitution extends at.logic.utils.logging.Logger {
  import ProofTransformationUtils.computeMap

  def toLabelledSequent( so: Sequent )
    = new LabelledSequent( so.antecedent.map( fo => fo.asInstanceOf[LabelledFormulaOccurrence] ),
                           so.succedent.map( fo => fo.asInstanceOf[LabelledFormulaOccurrence] ) )

def apply( proof: LKProof, subst: Substitution ) : (LKProof, Map[LabelledFormulaOccurrence, LabelledFormulaOccurrence]) =
  proof match {
    case Axiom(so : LabelledSequent) => {
      val ant_occs  = so.l_antecedent
      val succ_occs = so.l_succedent
      val seq = FSequent(ant_occs.map( fo => subst(fo.formula) ), succ_occs.map( fo => subst(fo.formula) ) )
      val labels_ant = ant_occs.map( fo => fo.skolem_label.map( t => subst(t) ) ).toList
      val labels_succ = succ_occs.map( fo => fo.skolem_label.map( t => subst(t) ) ).toList
      val (a, (antecedent, succedent)) = Axiom.createDefault(seq, Pair(labels_ant, labels_succ) )

      require(antecedent.length >= ant_occs.length, "cannot create translation map: old proof antecedent is shorter than new one")
      require(succedent.length >= succ_occs.length, "cannot create translation map: old proof succedent is shorter than new one")
      val map = Map[LabelledFormulaOccurrence, LabelledFormulaOccurrence]() ++
        (ant_occs zip antecedent) ++ (succ_occs zip succedent)

      (a, map)
    }
    case WeakeningLeftRule(p, s, m) => {
      val new_parent = apply( p, subst )
      val new_proof = WeakeningLeftRule.createDefault( new_parent._1, subst(m.formula), m.skolem_label.map( e => subst.apply(e) ) )
      val es = toLabelledSequent( p.root )
      ( new_proof, computeMap( es.l_antecedent ++ es.l_succedent, proof, new_proof, new_parent._2 ) + Pair(m, new_proof.prin.head ) )
    }
    case WeakeningRightRule(p, s, m) => {
      val new_parent = apply( p, subst )
      val new_proof = WeakeningRightRule.createDefault( new_parent._1, subst(m.formula), m.skolem_label.map( e => subst.apply(e) ) )
      val es = toLabelledSequent( p.root )
      ( new_proof, computeMap( es.l_antecedent ++ es.l_succedent, proof, new_proof, new_parent._2 ) + Pair(m, new_proof.prin.head ) )
    }
    case ForallSkLeftRule(p, s, a, m, t) => {
      val new_parent = apply( p, subst )
      val new_proof = ForallSkLeftRule( new_parent._1, new_parent._2(a), subst(m.formula), subst(t), !m.skolem_label.contains(t) )

      val es = toLabelledSequent( p.root )
      ( new_proof, computeMap( es.l_antecedent ++ es.l_succedent, proof, new_proof, new_parent._2 ) )
    }
    case ExistsSkRightRule(p, s, a, m, t) => {
      val new_parent = apply( p, subst )
      val new_proof = ExistsSkRightRule( new_parent._1, new_parent._2(a), subst(m.formula), subst.apply(t), !m.skolem_label.contains(t) )

      val es = toLabelledSequent( p.root )
      ( new_proof, computeMap( es.l_antecedent ++ es.l_succedent, proof, new_proof, new_parent._2 ) )
    }
    case ForallSkRightRule(p, s, a, m, t) => {
      val new_parent = apply( p, subst )
      val new_proof = ForallSkRightRule( new_parent._1, new_parent._2(a), subst(m.formula), subst.apply( t ) )
      val es = toLabelledSequent( p.root )
      ( new_proof, computeMap( es.l_antecedent ++ es.l_succedent, proof, new_proof, new_parent._2 ) )
    }
    case ExistsSkLeftRule(p, s, a, m, t) => {
      val new_parent = apply( p, subst )
      val new_proof = ExistsSkLeftRule( new_parent._1, new_parent._2(a), subst(m.formula), subst.apply( t ) )
      val es = toLabelledSequent( p.root )
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
}
