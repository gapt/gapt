/**
 * Terms extraction
 *
 * Returns a list with the terms used to instantiate each wekely quantified
 * formula.
 * Implemented for the cut-introduction algorithm.
 * NOTE: Prenex formulas only.
 TODO: explain this nicely
 // NOTE: Since we are dealing only with prenex formulas, it is not the case 
     // that aux1 or aux2 have instantiated formulas. Therefore, they were not 
     // added to the HashMap. It is not needed to alter the HashMap.
 */

import at.logic.calculi.lk.base._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.calculi.lk.definitionRules._
import at.logic.language.hol._
import at.logic.calculi.occurrences._
import scala.collection.immutable._
import at.logic.calculi.lk.base.types._

package herbrandExtraction {

class TermsExtractionException(msg: String) extends Exception(msg)

object termsExtraction {

  def apply(proof: LKProof) : List[Seq[HOLExpression]] = {
    val map = extractTerms(proof)
    var terms = Nil
    // Process the hashmap
    map.foreach(t => terms ++ t._2)
    terms
  }
  
  private def extractTerms(proof: LKProof) : HashMap[FormulaOccurrence, List[List[HOLExpression]]] = proof match {

    /* AXIOM */
    case Axiom(s) => new HashMap[FormulaOccurrence, List[List[HOLExpression]]] 

    /* WEAKENING RULES */
    case WeakeningLeftRule(up, _, pf) =>
      extractTerms(up)
    case WeakeningRightRule(up, _, pf) =>
      extractTerms(up)

    /* CONTRACTION RULES */
    case ContractionLeftRule(up, _, aux1, aux2, prin) =>
      val map = extractTerms(up)
      val t1 = map(aux1)
      val t2 = map(aux2)
      val auxmap = map - (aux1, aux2)
      // TODO: check this concatenation
      auxmap + (prin -> (t1 ++ t2))
    case ContractionRightRule(up, _, aux1, aux2, prin) =>
      val map = extractTerms(up)
      val t1 = map(aux1)
      val t2 = map(aux2)
      val auxmap = map - (aux1, aux2)
      // TODO: check this concatenation
      auxmap + (prin -> (t1 ++ t2))

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
      if(map.contains(aux)){
        val terms = map(aux)
        // Append the new terms to every list in terms
        terms.foreach(lst => lst :+ term)
        val auxmap = map - aux
        auxmap + (prin -> terms)
      }
      else {
        map + (prin -> ((term::Nil)::Nil))
      }
    case ExistsRightRule(up, _, aux, prin, term) =>
      val map = extractTerms(up)
      if(map.contains(aux)){
        val terms = map(aux)
        // Append the new terms to every list in terms
        terms.foreach(lst => lst :+ term)
        val auxmap = map - aux
        auxmap + (prin -> terms)
      }
      else {
        map + (prin -> ((term::Nil)::Nil))
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
}
