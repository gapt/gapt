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
import at.logic.calculi.lk.propositionalRules.{ImpLeftRule, AndRightRule, OrRight1Rule, ImpRightRule, WeakeningLeftRule => LKWeakeningLeftRule, OrRight2Rule, ContractionRightRule, WeakeningRightRule => LKWeakeningRightRule, OrLeftRule}
import at.logic.calculi.lk.base.{LKProof,Sequent,SequentOccurrence}
import at.logic.language.hol.propositions.TypeSynonyms._
import at.logic.language.hol.propositions._
import at.logic.language.hol.logicSymbols._
import at.logic.language.hol.quantifiers._
import at.logic.language.lambda.types._
import at.logic.language.lambda._
import at.logic.language.lambda.substitutions.SingleSubstitution
import at.logic.language.hol.substitutions._
import at.logic.algorithms.lksk.applySubstitution

object LKtoLKskc {
  // cut_occs is the set of cut-ancestors in the proof.
  def apply(proof: LKProof, cut_occs: Set[FormulaOccurrence]) = {
    // initialize map from occurrences to substitution terms:
    // in the end-sequent, there are no substitution terms for any
    // formula occurrences on the path to the end-sequent
    val subst_terms = new HashMap[FormulaOccurrence, Label]
    proof.root.antecedent.foreach( fo => subst_terms.update( fo, EmptyLabel() ) )
    proof.root.succedent.foreach( fo => subst_terms.update( fo, EmptyLabel() ) )
    rec( proof, subst_terms, cut_occs )._1
  }
  
  def rec(proof: LKProof, subst_terms: Map[FormulaOccurrence, Label], cut_occs: Set[FormulaOccurrence]) : (LKProof, Map[FormulaOccurrence,LabelledFormulaOccurrence]) = proof match {
    case LKAxiom(so) => {
      val ant = so.antecedent.toList
      val succ = so.succedent.toList
      val a = Axiom( Sequent( ant.map( fo => fo.formula ), succ.map( fo => fo.formula ) ),
                     Pair( ant.map( fo => subst_terms.apply( fo ) ), 
                           succ.map( fo => subst_terms.apply( fo ) ) ) )
      //assert( a._1.root.isInstanceOf[LabelledSequentOccurrence] )
      val map = new HashMap[FormulaOccurrence, LabelledFormulaOccurrence]
      a._2._1.zip(a._2._1.indices).foreach( p => map.update( ant( p._2 ), p._1 ) )
      a._2._2.zip(a._2._2.indices).foreach( p => map.update( succ( p._2 ), p._1 ) )
      (a._1, map)
    }
    case ForallLeftRule(p, s, a, m, t) => 
      if (!cut_occs.contains(m))
        transformWeakQuantRule( proof, subst_terms, p, a, m, t, (s.antecedent - m) ++ s.succedent,
                                cut_occs, ForallSkLeftRule.apply )
      else
        copyWeakQuantRule( proof, subst_terms, p, a, m, t, s, cut_occs, ForallLeftRule.apply )
    case ExistsRightRule(p, s, a, m, t) => 
      if (!cut_occs.contains(m))
        transformWeakQuantRule( proof, subst_terms, p, a, m, t, s.antecedent ++ (s.succedent - m), 
                                cut_occs, ExistsSkRightRule.apply )
      else
        copyWeakQuantRule( proof, subst_terms, p, a, m, t, s, cut_occs, ExistsRightRule.apply )
    case ForallRightRule(p, s, a, m, v) =>
      if (!cut_occs.contains(m))
      {
        val new_label_map = copyMapFromAncestor( s.antecedent ++ s.succedent, subst_terms )
        val r = rec( p, new_label_map, cut_occs )
        val newaux = r._2(a)
        val args = newaux.label.toList
        m.formula match {
          case All(_, t) => t match { case ( (alpha -> To()) -> To()) =>
            val f = getFreshSkolemFunctionSymbol
            val s = Function( f, args, alpha )
            val ssubst = new SingleSubstitution( v, s )
            println( "applying substitution: " + v.toStringSimple + " <- " + s.toStringSimple )
            val subst = new Substitution( ssubst::Nil )
            val new_parent = applySubstitution( r._1, subst )
            val new_proof = ForallSkRightRule(new_parent._1, new_parent._2(newaux), m.formula, s)
            //assert( new_proof.root.isInstanceOf[LabelledSequentOccurrence] )
            // TODO: casts are only due to Set/Map not being covariant!?
            val composed_map = r._2.clone
            composed_map.transform( (k, v) => new_parent._2( v ) )
            (new_proof, computeMap( p.root.antecedent.asInstanceOf[Set[FormulaOccurrence]] ++
                                    p.root.succedent.asInstanceOf[Set[FormulaOccurrence]], 
                                    proof, new_proof, composed_map ) )
          }
        }
      }
      else
      {
        val new_label_map = copyMapFromAncestor( s.antecedent ++ s.succedent, subst_terms )
        val r = rec( p, new_label_map, cut_occs )
        val sk_proof = ForallRightRule( r._1, r._2(a), m.formula, v )
        //assert( sk_proof.root.isInstanceOf[LabelledSequentOccurrence] )
        (sk_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, sk_proof, r._2 ) )
      }
    case ExistsLeftRule(p, s, a, m, v) =>
      if (!cut_occs.contains(m))
      {
        val new_label_map = copyMapFromAncestor( s.antecedent ++ s.succedent, subst_terms )
        val r = rec( p, new_label_map, cut_occs )
        val newaux = r._2(a)
        val args = newaux.label.toList
        m.formula match {
          case Ex(_, t) => t match { case ( (alpha -> To()) -> To()) =>
            val f = getFreshSkolemFunctionSymbol
            val s = Function( f, args, alpha )
            val ssubst = new SingleSubstitution( v, s )
            println( "applying substitution: " + v.toStringSimple + " <- " + s.toStringSimple )
            val subst = new Substitution( ssubst::Nil )
            val new_parent = applySubstitution( r._1, subst )
            val new_proof = ExistsSkLeftRule(new_parent._1, new_parent._2(newaux), m.formula, s)
            //assert( new_proof.root.isInstanceOf[LabelledSequentOccurrence] )
            // TODO: casts are only due to Set/Map not being covariant!?
            val composed_map = r._2.clone
            composed_map.transform( (k, v) => new_parent._2( v ) )
            (new_proof, computeMap( p.root.antecedent.asInstanceOf[Set[FormulaOccurrence]] ++
                                    p.root.succedent.asInstanceOf[Set[FormulaOccurrence]], 
                                    proof, new_proof, composed_map ) )
          }
        }
      }
      else
      {
        val new_label_map = copyMapFromAncestor( s.antecedent ++ s.succedent, subst_terms )
        val r = rec( p, new_label_map, cut_occs )
        val sk_proof = ExistsLeftRule( r._1, r._2(a), m.formula, v )
        //assert( sk_proof.root.isInstanceOf[LabelledSequentOccurrence] )
        (sk_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, sk_proof, r._2 ) )
      }
    case ImpLeftRule(p1, p2, s, a1, a2, m) => {
//      val new_label_map_1 = copyMapFromAncestor( 
//                              p1.root.antecedent.map( proof.getDescendantInLowerSequent(_).get ) ++
//                              p1.root.succedent.map( proof.getDescendantInLowerSequent(_).get ), 
//                              subst_terms )
//      val new_label_map_2 = copyMapFromAncestor(
//                              p2.root.antecedent.map( proof.getDescendantInLowerSequent(_).get ) ++
//                              p2.root.succedent.map( proof.getDescendantInLowerSequent(_).get ), 
//                              subst_terms )
      val new_label_map = copyMapFromAncestor( s.antecedent ++ s.succedent, subst_terms )
      val r1 = rec( p1, new_label_map, cut_occs )
      val r2 = rec( p2, new_label_map, cut_occs )
      val sk_proof = ImpLeftRule( r1._1, r2._1, r1._2( a1 ), r2._2( a2 ) )
      //assert( sk_proof.root.isInstanceOf[LabelledSequentOccurrence] )
      (sk_proof, computeMap( p1.root.antecedent ++ p1.root.succedent, proof, sk_proof, r1._2 ) ++
                 computeMap( p2.root.antecedent ++ p2.root.succedent, proof, sk_proof, r2._2 ) )
    }
    case AndRightRule(p1, p2, s, a1, a2, m) => {
//      val new_label_map_1 = copyMapFromAncestor( 
//                              p1.root.antecedent.map( proof.getDescendantInLowerSequent(_).get ) ++
//                              p1.root.succedent.map( proof.getDescendantInLowerSequent(_).get ), 
//                              subst_terms )
//      val new_label_map_2 = copyMapFromAncestor(
//                              p2.root.antecedent.map( proof.getDescendantInLowerSequent(_).get ) ++
//                              p2.root.succedent.map( proof.getDescendantInLowerSequent(_).get ), 
//                              subst_terms )
      val new_label_map = copyMapFromAncestor( s.antecedent ++ s.succedent, subst_terms )
      val r1 = rec( p1, new_label_map, cut_occs )
      val r2 = rec( p2, new_label_map, cut_occs )
      val sk_proof = AndRightRule( r1._1, r2._1, r1._2( a1 ), r2._2( a2 ) )
      //assert( sk_proof.root.isInstanceOf[LabelledSequentOccurrence] )
      (sk_proof, computeMap( p1.root.antecedent ++ p1.root.succedent, proof, sk_proof, r1._2 ) ++
                 computeMap( p2.root.antecedent ++ p2.root.succedent, proof, sk_proof, r2._2 ) )
    }
    case OrLeftRule(p1, p2, s, a1, a2, m) => {
//      val new_label_map_1 = copyMapFromAncestor( 
//                              p1.root.antecedent.map( proof.getDescendantInLowerSequent(_).get ) ++
//                              p1.root.succedent.map( proof.getDescendantInLowerSequent(_).get ), 
//                              subst_terms )
//      val new_label_map_2 = copyMapFromAncestor(
//                              p2.root.antecedent.map( proof.getDescendantInLowerSequent(_).get ) ++
//                              p2.root.succedent.map( proof.getDescendantInLowerSequent(_).get ), 
//                              subst_terms )
      val new_label_map = copyMapFromAncestor( s.antecedent ++ s.succedent, subst_terms )
      val r1 = rec( p1, new_label_map, cut_occs )
      val r2 = rec( p2, new_label_map, cut_occs )
      println( "label left: " )
      r1._2( a1 ).label.foreach( f => println( f.toStringSimple ) )
      println
      println( "label right: ")
      r2._2( a2 ).label.foreach( f => println( f.toStringSimple ) )
      val sk_proof = OrLeftRule( r1._1, r2._1, r1._2( a1 ), r2._2( a2 ) )
      //assert( sk_proof.root.isInstanceOf[LabelledSequentOccurrence] )
      (sk_proof, computeMap( p1.root.antecedent ++ p1.root.succedent, proof, sk_proof, r1._2 ) ++
                 computeMap( p2.root.antecedent ++ p2.root.succedent, proof, sk_proof, r2._2 ) )
    }
    case OrRight1Rule(p, s, a, m) => {
      val weak = m.formula match { case Or(_, w) => w }
      val new_label_map = copyMapFromAncestor( s.antecedent ++ s.succedent, subst_terms )
      val r = rec( p, new_label_map, cut_occs )
      //assert( r._1.root.isInstanceOf[LabelledSequentOccurrence] )
      val sk_proof = OrRight1Rule( r._1, r._2( a ), weak )
      //assert( sk_proof.root.isInstanceOf[LabelledSequentOccurrence] )
      (sk_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, sk_proof, r._2 ) )
    }
    case OrRight2Rule(p, s, a, m) => {
      val weak = m.formula match { case Or(w, _) => w }
      val new_label_map = copyMapFromAncestor( s.antecedent ++ s.succedent, subst_terms )
      val r = rec( p, new_label_map, cut_occs )
      val sk_proof = OrRight2Rule( r._1, weak, r._2( a ) )
      //assert( sk_proof.root.isInstanceOf[LabelledSequentOccurrence] )
      (sk_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, sk_proof, r._2 ) )
    }
    case ImpRightRule(p, s, a1, a2, m) => {
      val new_label_map = copyMapFromAncestor( s.antecedent ++ s.succedent, subst_terms )
      val r = rec( p, new_label_map, cut_occs )
      val sk_proof = ImpRightRule( r._1, r._2( a1 ), r._2( a2 ) )
      //assert( sk_proof.root.isInstanceOf[LabelledSequentOccurrence] )
      (sk_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, sk_proof, r._2 ) )
    }
    case LKWeakeningLeftRule(p, s, m) => {
      val new_label_map = copyMapFromAncestor( (s.antecedent - m) ++ s.succedent, subst_terms )
      val r = rec( p, new_label_map, cut_occs )
      val sk_proof = WeakeningLeftRule( r._1, m.formula, subst_terms.apply( m ) )
      //assert( sk_proof.root.isInstanceOf[LabelledSequentOccurrence] )
      (sk_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, sk_proof, r._2 ) +
                 Pair( m, sk_proof.prin.first ) )
    }
    case LKWeakeningRightRule(p, s, m) => {
      val new_label_map = copyMapFromAncestor( s.antecedent ++ (s.succedent - m), subst_terms )
      val r = rec( p, new_label_map, cut_occs )
      val sk_proof = WeakeningRightRule( r._1, m.formula, subst_terms.apply( m ) )
      //assert( sk_proof.root.isInstanceOf[LabelledSequentOccurrence] )
      (sk_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, sk_proof, r._2 ) +
                 Pair( m, sk_proof.prin.first ) )
    }
    case ContractionRightRule(p, s, a1, a2, m) => {
      val new_label_map = copyMapFromAncestor( s.antecedent ++ s.succedent, subst_terms )
      val r = rec( p, new_label_map, cut_occs )
      val sk_proof = ContractionRightRule( r._1, r._2( a1 ), r._2( a2 ) )
      //assert( sk_proof.root.isInstanceOf[LabelledSequentOccurrence] )
      (sk_proof, computeMap( p.root.antecedent ++ p.root.succedent, proof, sk_proof, r._2 ) )
    }
    // TODO: implement other propositional and structural rules!
  }

  def computeMap( occs: Set[FormulaOccurrence], old_proof: LKProof, 
                  new_proof: LKProof, old_map : Map[FormulaOccurrence, LabelledFormulaOccurrence]) =
  {
    val map = new HashMap[FormulaOccurrence, LabelledFormulaOccurrence]
    occs.foreach( fo => map.update( old_proof.getDescendantInLowerSequent( fo ).get, 
      new_proof.getDescendantInLowerSequent( old_map(fo) ).get.asInstanceOf[LabelledFormulaOccurrence] ) )
    map
  }

  def copyWeakQuantRule( proof: LKProof, subst_terms: Map[FormulaOccurrence, Label],
                         parent: LKProof, aux: FormulaOccurrence, main: FormulaOccurrence,
                         term: HOLTerm, end_seq: SequentOccurrence, cut_occs: Set[FormulaOccurrence],
                         constructor: (LKProof, FormulaOccurrence, Formula, HOLTerm) => LKProof ) = {
    val new_label_map = copyMapFromAncestor( end_seq.antecedent ++ end_seq.succedent, subst_terms )
    val r = rec( parent, new_label_map, cut_occs )
    val sk_proof = constructor( r._1, r._2(aux), main.formula, term )
    //assert( sk_proof.root.isInstanceOf[LabelledSequentOccurrence] )
    (sk_proof, computeMap( parent.root.antecedent ++ parent.root.succedent, proof, sk_proof, r._2 ) )
  }

  def transformWeakQuantRule( proof: LKProof, subst_terms: Map[FormulaOccurrence, Label],
                              parent: LKProof, aux: FormulaOccurrence, main: FormulaOccurrence,
                              term: HOLTerm, context: Set[FormulaOccurrence], cut_occs: Set[FormulaOccurrence],
                              constructor: (LKProof, LabelledFormulaOccurrence, Formula, HOLTerm, Boolean) => LKProof )
  = {
      val new_label_map = copyMapFromAncestor( context, subst_terms ) + Pair(aux, subst_terms(main) + term)
      val r = rec( parent, new_label_map, cut_occs )
      val sk_proof = constructor( r._1, r._2(aux), main.formula, term,
                                !subst_terms(main).contains(term) )
      //assert( sk_proof.root.isInstanceOf[LabelledSequentOccurrence] )
      (sk_proof, computeMap( parent.root.antecedent ++ parent.root.succedent, proof, sk_proof, r._2 ) )
    }


  def copyMapFromAncestor( fos: Set[FormulaOccurrence], map: Map[FormulaOccurrence, Label] ) : 
    Map[FormulaOccurrence, Label] = map ++ 
                                    fos.map( fo => Pair(fo.ancestors.first, map( fo ) ) ) ++ 
                                    fos.map( fo => Pair(fo.ancestors.last, map( fo ) ) )

  // TODO: implement this in a reasonable way!
  // Tomer suggested a skolem symbol trait to distinguish skolem symbols from normal symbols
  // regarding freshness: the user should probably supply the list of symbols that is in use
  var skolem_cnt = -1
  def getFreshSkolemFunctionSymbol = {
    skolem_cnt += 1
    ConstantStringSymbol( "s_{" + skolem_cnt + "}" )
  }
}
