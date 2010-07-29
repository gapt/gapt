/*
 * projections.scala
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package at.logic.transformations.ceres.projections

import at.logic.transformations.ceres.struct._
import at.logic.calculi.lk.base._
import at.logic.calculi.lksk.base._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.occurrences._
import scala.collection.immutable._
import at.logic.language.hol._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.definitionRules._
import at.logic.calculi.lk.equationalRules._
import at.logic.calculi.lk.base.{LKProof,Sequent,SequentOccurrence,PrincipalFormulas}

object Projections {
  def apply( proof: LKProof ) : Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] = apply( proof, new HashSet[FormulaOccurrence] )

  def apply( proof: LKProof, cut_ancs: Set[FormulaOccurrence] ) : Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] = proof match {
     case Axiom(s) => {
      // TODO: this is also used in the skolemization algorithm. refactor into Axiom.copy( proof )?
      val ant = s.antecedent.toList
      val succ = s.succedent.toList
      val new_seq = Sequent( ant.map( fo => fo.formula ), succ.map( fo => fo.formula ) )
      val ax = Axiom( new_seq )
      var new_map = ant.zipWithIndex.foldLeft(new HashMap[FormulaOccurrence, FormulaOccurrence])( (m, p) => m + ( p._1 -> ax._2._1( p._2 ) ))
      new_map = succ.zipWithIndex.foldLeft(new_map)((m, p) => m + ( p._1 -> ax._2._2( p._2 )))

      new HashSet[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] + Pair(ax._1, new_map)
    }
    case ForallRightRule(p, _, a, m, v) => handleStrongQuantRule( proof, p, a, m, v, ForallRightRule.apply, cut_ancs )
    case ExistsLeftRule(p, _, a, m, v) => handleStrongQuantRule( proof, p, a, m, v, ExistsLeftRule.apply, cut_ancs )
    /*
    case ForallLeftRule(p, _, a, m, t) => handleWeakQuantRule( proof, p, a, m, t, ForallLeftRule.computeAux,
      ForallLeftRule.apply)
    case ExistsRightRule(p, _, a, m, t) => handleWeakQuantRule( proof, p, a, m, t, ExistsRightRule.computeAux,
      ExistsRightRule.apply)
    case WeakeningLeftRule(p, _, m) => handleWeakeningRule( proof, p, m, WeakeningLeftRule.apply)
    case WeakeningRightRule(p, _, m) => handleWeakeningRule( proof, p, m, WeakeningRightRule.apply)
    case ContractionLeftRule(p, _, a1, a2, _) => handleContractionRule( proof, p, a1, a2, ContractionLeftRule.apply)
    case ContractionRightRule(p, _, a1, a2, _) => handleContractionRule( proof, p, a1, a2, ContractionRightRule.apply)
    case AndRightRule(p1, p2, _, a1, a2, m) => handleBinaryRule( proof, p1, p2, a1, a2, m, AndRightRule.computeLeftAux, AndRightRule.computeRightAux, AndRightRule.apply)
    case AndLeft1Rule(p, _, a, m) => handleUnaryRule( proof, p, a, 
      form_map( m ) match { case And(_, w) => w }, m, AndLeft1Rule.computeAux, AndLeft1Rule.apply)
    case AndLeft2Rule(p, _, a, m) => handleUnary2Rule( proof, p, a,
      form_map( m ) match { case And(w, _) => w }, m, AndLeft2Rule.computeAux, AndLeft2Rule.apply)
    case OrLeftRule(p1, p2, _, a1, a2, m) => handleBinaryRule( proof, p1, p2, a1, a2, m, OrLeftRule.computeLeftAux, OrLeftRule.computeRightAux, OrLeftRule.apply)
    case OrRight1Rule(p, _, a, m) => handleUnaryRule( proof, p, a,
      form_map( m ) match { case Or(_, w) => w }, m, OrRight1Rule.computeAux, OrRight1Rule.apply)
    case OrRight2Rule(p, _, a, m) => handleUnary2Rule( proof, p, a,
      form_map( m ) match { case Or(w, _) => w }, m, OrRight2Rule.computeAux, OrRight2Rule.apply)
    case ImpLeftRule(p1, p2, _, a1, a2, m) => handleBinaryRule( proof, p1, p2, a1, a2, m, ImpLeftRule.computeLeftAux, ImpLeftRule.computeRightAux, ImpLeftRule.apply)
    case ImpRightRule(p, _, a1, a2, m) => {
      val (na1, na2) = form_map(m) match { case Imp(l, r) => (l, r) }
      val new_proof = skolemize( p, copyMapToAncestor(symbol_map), copyMapToAncestor(inst_map),
        copyMapToAncestor(form_map).updated(a1, na1).updated(a2, na2), copySetToAncestor( cut_ancs ) )
      val ret = ImpRightRule( new_proof._1, new_proof._2( a1 ), new_proof._2( a2 ) )
      (ret, copyMapToDescendant( proof, ret, new_proof._2 ))
    }
    case NegLeftRule( p, _, a, m ) => handleNegRule( proof, p, a, m, NegLeftRule.computeAux, NegLeftRule.apply )
    case NegRightRule( p, _, a, m ) => handleNegRule( proof, p, a, m, NegLeftRule.computeAux, NegRightRule.apply )
    case DefinitionLeftRule( p, _, a, m ) => handleDefRule( proof, p, a, m, 1, DefinitionLeftRule.apply )
    case DefinitionRightRule( p, _, a, m ) => handleDefRule( proof, p, a, m, 0, DefinitionRightRule.apply )
    case EquationLeft1Rule( p1, p2, _, e, a, m ) => handleEqRule( proof, p1, p2, e, a, m, 1, EquationLeft1Rule.apply )
    case EquationLeft2Rule( p1, p2, _, e, a, m ) => handleEqRule( proof, p1, p2, e, a, m, 1, EquationLeft2Rule.apply )
    case EquationRight1Rule( p1, p2, _, e, a, m ) => handleEqRule( proof, p1, p2, e, a, m, 1, EquationRight1Rule.apply )
    case EquationRight2Rule( p1, p2, _, e, a, m ) => handleEqRule( proof, p1, p2, e, a, m, 1, EquationRight2Rule.apply )
    */
    case CutRule( p1, p2, _, a1, a2 ) => {
      val new_cut_ancs = copySetToAncestor( cut_ancs )
      val s1 = apply( p1, new_cut_ancs + a1 )
      val s2 = apply( p2, new_cut_ancs + a2 )
      copyMapsToDescendant( proof, s1 ) ++ copyMapsToDescendant( proof, s2 )
    }
  }

  def handleStrongQuantRule( proof: LKProof, p: LKProof, a: FormulaOccurrence, m: FormulaOccurrence, v: HOLVar,
    constructor: (LKProof, FormulaOccurrence, HOLFormula, HOLVar) => LKProof,
    cut_ancs: Set[FormulaOccurrence]) : Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] = {
    val s = apply( p, copySetToAncestor( cut_ancs ) )
    s.map( p => {
      val new_proof = constructor( p._1, p._2( a ), m.formula, v )
      val new_map = copyMapToDescendant( proof, p._1, p._2 )
      (new_proof, new_map)
    })
  }

  def copyMapsToDescendant( proof: LKProof, s: Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])]) : Set[(LKProof, Map[FormulaOccurrence, FormulaOccurrence])] =
    s.map( p => (p._1, copyMapToDescendant( proof, p._1, p._2 ) ) )

  // TODO: the following 3 are taken from skolemization.scala --- refactor!
  def copyMapToAncestor[A]( map: Map[FormulaOccurrence, A] ) =
    map.foldLeft(new HashMap[FormulaOccurrence, A])( (m, p) => m ++ p._1.ancestors.map( a => (a, p._2) ) )
 
  def copySetToAncestor( set: Set[FormulaOccurrence] ) = set.foldLeft( new HashSet[FormulaOccurrence] )( (s, fo) => s ++ fo.ancestors )

  def copyMapToDescendant( old_p: LKProof, new_p: LKProof, 
                           map: Map[FormulaOccurrence, FormulaOccurrence] ) =
    map.foldLeft(new HashMap[FormulaOccurrence, FormulaOccurrence])( (m, p) => {
        val desc = old_p.getDescendantInLowerSequent( p._1 )
        if (desc != None)
          m + (desc.get -> new_p.getDescendantInLowerSequent( p._2 ).get )
        else
          m
      } )

}
