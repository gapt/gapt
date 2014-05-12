/**
 * Terms extraction
 *
 * Returns a list with the terms used to instantiate each weakly quantified
 * formula.
 * Implemented for the cut-introduction algorithm.
 * NOTE: This algorithm was developed for prenex formulas only.
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
import at.logic.transformations.herbrandExtraction._

class TermsExtractionException(msg: String) extends Exception(msg)

object TermsExtraction {

  // If all the quantified formulas have only one quantifier, each list of
  // the list will have only one element
  def apply(proof: LKProof) : Map[FOLFormula, List[List[FOLTerm]]] = apply(extractExpansionTrees(proof))

  // An expansion proof is a pair of expansion trees, one for each formula in
  // the antecedent and succedent of the end-sequent
  def apply(expProof: ExpansionSequent) : Map[FOLFormula, List[List[FOLTerm]]] = {
    
    // Transform to a list of MultiExpansionTrees
    val multiExpTrees = (expProof.antecedent.map(et => compressQuantifiers(et))) ++ (expProof.succedent.map(et => compressQuantifiers(et)))

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
}

