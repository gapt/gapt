/**
 * Terms extraction
 *
 * Returns a list with the terms used to instantiate each weakly quantified
 * formula.
 * Implemented for the cut-introduction algorithm.
 * NOTE: This algorithm was developed for prenex formulas only.
 * This means that when we hava a binary rule such as A ^ B, it is never the
 * case that A or B have instantiated terms. Therefore, we don't worry about it
 * and don't look them up on the hashmap (they won't be there anyway...)
 */

package at.logic.algorithms.cutIntroduction

import at.logic.calculi.lk.base._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.definitionRules._
import at.logic.language.fol._
import at.logic.calculi.occurrences._
import scala.collection.immutable._
import at.logic.calculi.lk.base.types._
import at.logic.algorithms.lk._

class TermsExtractionException(msg: String) extends Exception(msg)

object termsExtraction {

  // If all the quantified formulas have only one quantifier, each sequent of
  // the list will have only one element
  def apply(proof: LKProof) : HashMap[FormulaOccurrence, List[List[FOLTerm]]] = {
    val map = extractTerms(proof)
    map
    // Process the hashmap
    //val terms = map.foldRight(List[List[FOLTerm]]()){(t, acc) =>
    //  acc ++ t._2
    //}
    //terms
  }
  
  private def extractTerms(proof: LKProof) : HashMap[FormulaOccurrence, List[List[FOLTerm]]] = proof match {

    /* AXIOM */
    case Axiom(s) => new HashMap[FormulaOccurrence, List[List[FOLTerm]]] 

    /* WEAKENING RULES */
    case WeakeningLeftRule(up, _, pf) =>
      extractTerms(up)
    case WeakeningRightRule(up, _, pf) =>
      extractTerms(up)

    /* CONTRACTION RULES */
    case ContractionLeftRule(up, _, aux1, aux2, prin) =>
      val map = extractTerms(up)
      val ancestorsAux1 = getAncestors(aux1)
      val ancestorsAux2 = getAncestors(aux2)
      val keys = map.keys
      // Gets all the ancestors that are keys in the hashmap
      val anc1 = keys.filter(x => ancestorsAux1.contains(x)).toList
      val anc2 = keys.filter(x => ancestorsAux2.contains(x)).toList
      if (anc1.length == 1 && anc2.length == 1) {
        val a1 = anc1(0)
        val a2 = anc2(0)
        val t1 = map(a1)
        val t2 = map(a2)
        val auxmap = map - (a1, a2)
        val auxmap2 = auxmap + (prin -> (t1 ++ t2))
        auxmap2
      }
      else if (anc1.length == 1 && anc2.length == 0) {
        val a1 = anc1(0)
        val t = map(a1)
        val auxmap = map - (a1)
        val auxmap2 = auxmap + (prin -> t)
        auxmap2
      }
      else if (anc1.length == 0 && anc2.length == 1) {
        val a2 = anc2(0)
        val t = map(a2)
        val auxmap = map - (a2)
        val auxmap2 = auxmap + (prin -> t)
        auxmap2
      }
      else if (anc1.length > 0 && anc2.length > 1) {
        throw new TermsExtractionException("ERROR: More than one ancestor was instantiated.")
      }
      else map
    case ContractionRightRule(up, _, aux1, aux2, prin) =>
      val map = extractTerms(up)
      val ancestorsAux1 = getAncestors(aux1)
      val ancestorsAux2 = getAncestors(aux2)
      val keys = map.keys
      // Gets all the ancestors that are keys in the hashmap
      val anc1 = keys.filter(x => ancestorsAux1.contains(x)).toList
      val anc2 = keys.filter(x => ancestorsAux2.contains(x)).toList

      if (anc1.length == 1 && anc2.length == 1) {
        val a1 = anc1(0)
        val a2 = anc2(0)
        val t1 = map(a1)
        val t2 = map(a2)
        val auxmap = map - (a1, a2)
        val auxmap2 = auxmap + (prin -> (t1 ++ t2))
        auxmap2
      }
      else if (anc1.length == 1 && anc2.length == 0) {
        val a1 = anc1(0)
        val t = map(a1)
        val auxmap = map - (a1)
        val auxmap2 = auxmap + (prin -> t)
        auxmap2
      }
      else if (anc1.length == 0 && anc2.length == 1) {
        val a2 = anc2(0)
        val t = map(a2)
        val auxmap = map - (a2)
        val auxmap2 = auxmap + (prin -> t)
        auxmap2
      }
      else if (anc1.length > 0 && anc2.length > 1) {
        throw new TermsExtractionException("ERROR: More than one ancestor was instantiated.")
      }
      else map
 

    /* RIGHT CONJUNCTION RULE */
    case AndRightRule(up1, up2, _, aux1, aux2, _) =>
      val map1 = extractTerms(up1)
      val map2 = extractTerms(up2)
      map1 ++ map2

    /* LEFT CONJUNCTION RULES */
    case AndLeft1Rule(up, _, aux, prin) =>
      extractTerms(up)
    case AndLeft2Rule(up, _, aux, prin) =>
      extractTerms(up)

    /* LEFT DISJUNCTION RULE */
    case OrLeftRule(up1, up2, _, aux1, aux2, _) =>
      val map1 = extractTerms(up1)
      val map2 = extractTerms(up2)
      map1 ++ map2

    /* RIGHT DISJUNCTION RULES */
    case OrRight1Rule(up, _, aux, prin) =>
      extractTerms(up)
    case OrRight2Rule(up, _, aux, prin) =>
      extractTerms(up)

    /* LEFT IMPLICATION RULE */
    case ImpLeftRule(up1, up2, _, aux1, aux2, _) =>
      val map1 = extractTerms(up1)
      val map2 = extractTerms(up2)
      map1 ++ map2

    /* RIGHT IMPLICATION RULE */
    case ImpRightRule(up, _, aux1, aux2, _) =>
      extractTerms(up)

    /* NEGATION RULES */
    case NegLeftRule(up, _, aux, _) =>
      extractTerms(up)
    case NegRightRule(up, _, aux, _) =>
      extractTerms(up)

    /* WEAK QUANTIFIER RULES */
    // This is when the HashMap is filled.
    case ForallLeftRule(up, _, aux, prin, term) =>
      val map = extractTerms(up)
      val ancestorsAux = getAncestors(aux)
      val keys = map.keys
      val anc = keys.filter(x => ancestorsAux.contains(x)).toList
      if(anc.length == 1){
        val a = anc(0)
        val terms = map(a)
        // Append the new terms to every list in terms
        terms.foreach(lst => lst :+ term)
        val auxmap = map - a
        val auxmap2 = auxmap + (prin -> terms)
        auxmap2
      }
      else {
        val folterm = term.asInstanceOf[FOLTerm]
        val auxmap = map + (prin -> ((folterm::Nil)::Nil))
        auxmap
      }
    case ExistsRightRule(up, _, aux, prin, term) =>
      val map = extractTerms(up)
      val ancestorsAux = getAncestors(aux)
      val keys = map.keys
      val anc = keys.filter(x => ancestorsAux.contains(x)).toList
      if(anc.length == 1){
        val a = anc(0)
        val terms = map(a)
        // Append the new terms to every list in terms
        terms.foreach(lst => lst :+ term)
        val auxmap = map - a
        auxmap + (prin -> terms)
      }
      else {
        val folterm = term.asInstanceOf[FOLTerm]
        map + (prin -> ((folterm::Nil)::Nil))
      }

    /* CUT RULE */
    case CutRule(up1, up2, _, a1, a2) => 
      val map1 = extractTerms(up1)
      val map2 = extractTerms(up2)
      map1 ++ map2


    /* STRONG QUANTIFIER RULES */
    // Should not occur
    case ExistsLeftRule(_, _, _, _, _) | ForallRightRule(_, _, _, _, _) =>
      throw new TermsExtractionException("ERROR: Found strong quantifier rule while extracting terms.")

  }
}

