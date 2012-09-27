/*
 *  Extended Herbrand Sequent implementation
 *
 *  For more details on what this is, see: Towards Algorithmic Cut Introduction
 *  (S. Hetzl, A. Leitsch, D. Weller - LPAR-18, 2012)
 *
 */

package at.logic.algorithms.cutIntroduction

import at.logic.calculi.occurrences._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.language.fol._
import at.logic.language.fol.Utils._
import at.logic.algorithms.shlk._
import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._

// NOTE: implemented for the one cut case.
class ExtendedHerbrandSequent {
  
  // Instanciated (previously quantified) formulas on the left
  var inst_l : List[FOLFormula] = Nil
  // Instanciated (previously quantified) formulas on the right
  var inst_r : List[FOLFormula] = Nil
  // Propositional formulas on the left
  var prop_l : List[FOLFormula] = Nil
  // Propositional formulas on the right
  var prop_r : List[FOLFormula] = Nil

  var cutFormula : FOLFormula = null
  var decomposition : Decomposition = null
 
  // NOTE: s should be prenex and skolemized 
  def apply(s: Sequent, d: Decomposition) = {

    decomposition = d
    // From ".map" on are lots of castings just to make the data structure right :-|
    // FormulaOccurrence to HOLFormula to FOLFormula and Seq to List...
    prop_l = s.antecedent.filter(x => !x.formula.containsQuantifier).map(x => x.formula.asInstanceOf[FOLFormula]).toList
    prop_r = s.succedent.filter(x => !x.formula.containsQuantifier).map(x => x.formula.asInstanceOf[FOLFormula]).toList
    
    val quant_l = s.antecedent.filter(x => x.formula.containsQuantifier)
    val quant_r = s.succedent.filter(x => x.formula.containsQuantifier)

    inst_l = quant_l.foldRight(List[FOLFormula]()) {case (f, acc) => 
      val terms = decomposition.getUTermsOfFormula(f)
      terms.map(t => f.formula.asInstanceOf[FOLFormula].substituteAll(t)) ++ acc
    }
    inst_r = quant_r.foldRight(List[FOLFormula]()) {case (f, acc) => 
      val terms = decomposition.getUTermsOfFormula(f)
      terms.map(t => f.formula.asInstanceOf[FOLFormula].substituteAll(t)) ++ acc
    }
  }

/* TODO: uncomment and use once Autoprop returns Option[LKProof]
  // Checks if the sequent is a tautology using f as the cut formula
  def isValidWith(f: FOLFormula) : Boolean = {

    val body = f.substitute(decomposition.getVariable)

    val as = decomposition.getSTerms.foldRight(List[FOLFormula]()) {case (t, acc) =>
      acc :+ f.substitute(t) 
    }
    val head = conjunction(as)

    val impl = Imp(body, head)

    val antecedent = this.prop_l ++ this.inst_l :+ impl
    val succedent = this.prop_r ++ this.inst_r

    Autoprop(FSequent(antecedent, succedent)) match {
      case Some(proof) => true
      case None => false
    }
  }
*/
}

