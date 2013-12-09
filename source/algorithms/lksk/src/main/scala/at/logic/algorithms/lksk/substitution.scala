package at.logic.algorithms.lksk


import at.logic.calculi.lksk._
import at.logic.calculi.lksk.base._
import at.logic.calculi.occurrences.FormulaOccurrence
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.base.types._
import at.logic.calculi.lk.lkExtractors.{UnaryLKProof, BinaryLKProof}
import at.logic.language.hol._
import at.logic.algorithms.lk.{applySubstitution => LKapplySubstitution, ProofTransformationUtils}
import at.logic.language.lambda.substitutions.Substitution
import scala.collection.mutable

object applySubstitution extends at.logic.utils.logging.Logger {
  import ProofTransformationUtils.computeMap


  def toLabelledSequent( so: Sequent )
    = new LabelledSequent( so.antecedent.map( fo => fo.asInstanceOf[LabelledFormulaOccurrence] ),
                           so.succedent.map( fo => fo.asInstanceOf[LabelledFormulaOccurrence] ) )

def apply( proof: LKProof, subst: Substitution[HOLExpression] ) : (LKProof, Map[LabelledFormulaOccurrence, LabelledFormulaOccurrence]) =
  proof match {
    case Axiom(so : LabelledSequent) => {
      val ant_occs  = so.l_antecedent
      val succ_occs = so.l_succedent
      val (a, (antecedent, succedent)) = Axiom.createDefault(new FSequent(ant_occs.map( fo => subst(fo.formula).asInstanceOf[HOLFormula] ), succ_occs.map( fo => subst(fo.formula).asInstanceOf[HOLFormula] ) ),
        Pair( ant_occs.map( fo => fo.skolem_label.map( t => subst.apply(t) ) ).toList,
              succ_occs.map( fo => fo.skolem_label.map( t => subst.apply(t) ) ).toList ) )
      //val map = new mutable.HashMap[LabelledFormulaOccurrence, LabelledFormulaOccurrence]
      //a._2._1.zip(a._2._1.indices).foreach( p => map.update( ant_occs( p._2 ), p._1 ) )
      //a._2._2.zip(a._2._2.indices).foreach( p => map.update( succ_occs( p._2 ), p._1 ) )

      require(antecedent.length >= ant_occs.length, "cannot create translation map: old proof antecedent is shorter than new one")
      require(succedent.length >= succ_occs.length, "cannot create translation map: old proof succedent is shorter than new one")
      val map = Map[LabelledFormulaOccurrence, LabelledFormulaOccurrence]() ++
        (ant_occs zip antecedent) ++ (succ_occs zip succedent)

      (a, map)
    }
    case WeakeningLeftRule(p, s, m) => {
      val new_parent = apply( p, subst )
      val new_proof = WeakeningLeftRule.createDefault( new_parent._1, subst(m.formula).asInstanceOf[HOLFormula], m.skolem_label.map( e => subst.apply(e) ) )
      val es = toLabelledSequent( p.root )
      ( new_proof, computeMap( es.l_antecedent ++ es.l_succedent, proof, new_proof, new_parent._2 ) + Pair(m, new_proof.prin.head ) )
    }
    case WeakeningRightRule(p, s, m) => {
      val new_parent = apply( p, subst )
      val new_proof = WeakeningRightRule.createDefault( new_parent._1, subst(m.formula).asInstanceOf[HOLFormula], m.skolem_label.map( e => subst.apply(e) ) )
      val es = toLabelledSequent( p.root )
      ( new_proof, computeMap( es.l_antecedent ++ es.l_succedent, proof, new_proof, new_parent._2 ) + Pair(m, new_proof.prin.head ) )
    }
    case ForallSkLeftRule(p, s, a, m, t) => {
      val new_parent = apply( p, subst )
      val new_proof = ForallSkLeftRule( new_parent._1, new_parent._2(a), subst(m.formula).asInstanceOf[HOLFormula], subst.apply(t), !m.skolem_label.contains(t) )
      //assert(new_proof.prin(0).skolem_label.size == m.skolem_label.size )
      val es = toLabelledSequent( p.root )
      ( new_proof, computeMap( es.l_antecedent ++ es.l_succedent, proof, new_proof, new_parent._2 ) )
    }
    case ExistsSkRightRule(p, s, a, m, t) => {
      val new_parent = apply( p, subst )
      val new_proof = ExistsSkRightRule( new_parent._1, new_parent._2(a), subst(m.formula).asInstanceOf[HOLFormula], subst.apply(t), !m.skolem_label.contains(t) )
      //assert(new_proof.prin(0).skolem_label.size == m.skolem_label.size )
      val es = toLabelledSequent( p.root )
      ( new_proof, computeMap( es.l_antecedent ++ es.l_succedent, proof, new_proof, new_parent._2 ) )
    }
    case ForallSkRightRule(p, s, a, m, t) => {
      val new_parent = apply( p, subst )
      val new_proof = ForallSkRightRule( new_parent._1, new_parent._2(a), subst(m.formula).asInstanceOf[HOLFormula], subst.apply( t ) )
      val es = toLabelledSequent( p.root )
      ( new_proof, computeMap( es.l_antecedent ++ es.l_succedent, proof, new_proof, new_parent._2 ) )
    }
    case ExistsSkLeftRule(p, s, a, m, t) => {
      val new_parent = apply( p, subst )
      val new_proof = ExistsSkLeftRule( new_parent._1, new_parent._2(a), subst(m.formula).asInstanceOf[HOLFormula], subst.apply( t ) )
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

  // TODO: a very similar method is used in LKtoLKskc, refactor!?
  /*
  def computeMap( occs: Seq[LabelledFormulaOccurrence], old_proof: LKProof, 
                  new_proof: LKProof, old_map : mutable.Map[LabelledFormulaOccurrence, LabelledFormulaOccurrence]) =
  {
    val map = new mutable.HashMap[LabelledFormulaOccurrence, LabelledFormulaOccurrence]
    occs.foreach( fo => map.update( old_proof.getDescendantInLowerSequent( fo ).get.asInstanceOf[LabelledFormulaOccurrence], 
      new_proof.getDescendantInLowerSequent( old_map(fo) ).get.asInstanceOf[LabelledFormulaOccurrence] ) )
    map
  } */
}
