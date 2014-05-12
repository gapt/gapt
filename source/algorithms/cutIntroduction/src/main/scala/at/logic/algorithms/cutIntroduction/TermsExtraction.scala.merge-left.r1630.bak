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
import at.logic.calculi.lk.equationalRules._
import at.logic.language.fol._
import at.logic.calculi.occurrences._
import scala.collection.immutable.HashMap
import at.logic.calculi.lk.base.types._
import at.logic.calculi.expansionTrees._
import at.logic.calculi.expansionTrees.multi.{WeakQuantifier => WeakQuantifierMulti, StrongQuantifier => StrongQuantifierMulti, toFormulaM}
import at.logic.algorithms.lk._
import at.logic.algorithms.expansionTrees._

class TermsExtractionException(msg: String) extends Exception(msg)

object TermsExtraction {

  // If all the quantified formulas have only one quantifier, each list of
  // the list will have only one element
  // TODO: make this method use the apply for expansionTree by extracting this
  // tree from the proof
  def apply(proof: LKProof) : Map[FOLFormula, List[List[FOLTerm]]] = {
    val es = proof.root
    val formulas = es.antecedent ++ es.succedent
    // Check if all formulas are prenex.
    if( formulas.forall(f => f.formula.isPrenex) ) {
      val map = extractTerms(proof)
      map
    }
    else throw new TermsExtractionException("ERROR: Trying to extract the terms of a proof with non-prenex formulas: " + es.toString)
  }

  // An expansion proof is a pair of expansion trees, one for each formula in
  // the antecedent and succedent of the end-sequent
  def apply(expProof: (Seq[ExpansionTree], Seq[ExpansionTree])) : Map[FOLFormula, List[List[FOLTerm]]] = {
    
    // Transform to a list of MultiExpansionTrees
    val multiExpTrees = (expProof._1.map(et => compressQuantifiers(et))) ++ (expProof._2.map(et => compressQuantifiers(et)))

    // Extract the terms
    multiExpTrees.foldRight( HashMap[FOLFormula, List[List[FOLTerm]]]() ) {case (mTree, map) =>
      if(toFormulaM(mTree).isPrenex) {
        mTree match {
          case WeakQuantifierMulti(form, children) => 
            val f = form.asInstanceOf[FOLFormula]
            val terms = children.map{ case (tree, termsSeq) => termsSeq.map(t => t.asInstanceOf[FOLTerm]).toList}.toList
            if(map.contains(f) ) {
              val t = map(f)
              map + (f -> (t ++ terms) )
            }
            else map + (f -> terms)
          case StrongQuantifierMulti(_,_,_) => throw new TermsExtractionException("ERROR: Found strong quantifier while extracting terms.")
          case _ => map
        }
      }
      else throw new TermsExtractionException("ERROR: Trying to extract the terms of an expansion proof with non-prenex formulas.")
    }
  }
 
  // Merges maps coming from different branches adding the lists of terms of equal formulas
  private def merge(m1: Map[FOLFormula, List[List[FOLTerm]]], m2: Map[FOLFormula, List[List[FOLTerm]]]) 
  : Map[FOLFormula, List[List[FOLTerm]]]= {
    val k1 = m1.keys.toSet
    val k2 = m2.keys.toSet
    val intersection = k1 & k2

    val r1 = for(key <- intersection) yield (key -> (m1(key) ++ m2(key)) )
    val r2 = m1.filterKeys(!intersection.contains(_)) ++ m2.filterKeys(!intersection.contains(_))
    r2 ++ r1
  }

  private def extractTerms(proof: LKProof) : Map[FOLFormula, List[List[FOLTerm]]] = proof match {

    /* AXIOM */
    case Axiom(_) => new HashMap[FOLFormula, List[List[FOLTerm]]] 

    /* WEAKENING RULES */
    case WeakeningLeftRule(up, _, pf) =>
      extractTerms(up)
    case WeakeningRightRule(up, _, pf) =>
      extractTerms(up)

    /* CONTRACTION RULES */
    case ContractionLeftRule(up, _, aux1, aux2, prin) =>
      extractTerms(up)

    case ContractionRightRule(up, _, aux1, aux2, prin) =>
      extractTerms(up)

    /* RIGHT CONJUNCTION RULE */
    case AndRightRule(up1, up2, _, aux1, aux2, _) =>
      val map1 = extractTerms(up1)
      val map2 = extractTerms(up2)
      merge(map1, map2)

    /* LEFT CONJUNCTION RULES */
    case AndLeft1Rule(up, _, aux, prin) =>
      extractTerms(up)
    case AndLeft2Rule(up, _, aux, prin) =>
      extractTerms(up)

    /* LEFT DISJUNCTION RULE */
    case OrLeftRule(up1, up2, _, aux1, aux2, _) =>
      val map1 = extractTerms(up1)
      val map2 = extractTerms(up2)
      merge(map1, map2)

    /* RIGHT DISJUNCTION RULES */
    case OrRight1Rule(up, _, aux, prin) =>
      extractTerms(up)
    case OrRight2Rule(up, _, aux, prin) =>
      extractTerms(up)

    /* LEFT IMPLICATION RULE */
    case ImpLeftRule(up1, up2, _, aux1, aux2, _) =>
      val map1 = extractTerms(up1)
      val map2 = extractTerms(up2)
      merge(map1, map2)

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
      val f = prin.formula.asInstanceOf[FOLFormula]
      val a = aux.formula.asInstanceOf[FOLFormula]
      val (map2, newterms) = if (map.contains(a) ) {
        val terms = map(a)
        // Append the new terms to every list in terms
        ((map-a), terms.map(lst => term.asInstanceOf[FOLTerm] :: lst))
      }
      else {
        val folterm = term.asInstanceOf[FOLTerm]
        (map, ((folterm::Nil)::Nil))
      }

      if(map2.contains(f) ) {
        val t = map2(f)
        map2 + (f -> (t ++ newterms) )
      }
      else map2 + (f -> newterms)

    case ExistsRightRule(up, _, aux, prin, term) =>
      val map = extractTerms(up)
      val f = prin.formula.asInstanceOf[FOLFormula]
      val a = aux.formula.asInstanceOf[FOLFormula]
      val (map2, newterms) = if (map.contains(a) ) {
        val terms = map(a)
        // Append the new terms to every list in terms
        ((map-a), terms.map(lst => term.asInstanceOf[FOLTerm] :: lst))
      }
      else {
        val folterm = term.asInstanceOf[FOLTerm]
        (map, ((folterm::Nil)::Nil))
      }

      if(map2.contains(f) ) {
        val t = map2(f)
        map2 + (f -> (t ++ newterms) )
      }
      else map2 + (f -> newterms)

    /* CUT RULE */
    case CutRule(up1, up2, _, a1, a2) => 
      val map1 = extractTerms(up1)
      val map2 = extractTerms(up2)
      merge(map1, map2)


    /* STRONG QUANTIFIER RULES */
    // Should not occur
    case ExistsLeftRule(_, _, _, _, _) | ForallRightRule(_, _, _, _, _) =>
      throw new TermsExtractionException("ERROR: Found strong quantifier while extracting terms.")

    /* EQUALITY RULES */
    // Not sure how to treat them... just skipping for now but this might cause problems in the future
    case EquationLeft1Rule(up1, up2, _, _, _, _) =>
      println("WARNING: found equality rule.")
      merge(extractTerms(up1), extractTerms(up2))
    case EquationLeft2Rule(up1, up2, _, _, _, _) =>
      println("WARNING: found equality rule.")
      merge(extractTerms(up1), extractTerms(up2))
    case EquationRight1Rule(up1, up2, _, _, _, _) =>
      println("WARNING: found equality rule.")
      merge(extractTerms(up1), extractTerms(up2))
    case EquationRight2Rule(up1, up2, _, _, _, _) =>
      println("WARNING: found equality rule.")
      merge(extractTerms(up1), extractTerms(up2))

    /* Any other rule... fail */
    case _ => throw new TermsExtractionException("ERROR: Unexpected rule while extracting the term set.\n" + proof.toString.substring(0, 20))
  }
}

