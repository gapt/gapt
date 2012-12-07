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
import at.logic.algorithms.lk._
import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._

// NOTE: implemented for the one cut case.
// NOTE2: s should be prenex and skolemized 
class ExtendedHerbrandSequent(seq: Sequent, d: (List[FOLTerm], List[FOLTerm]), flatterms: FlatTermSet) {
  
  // From ".map" on are lots of castings just to make the data structure right :-|
  // FormulaOccurrence to HOLFormula to FOLFormula and Seq to List...
  
  // Propositional formulas on the left
  val prop_l : List[FOLFormula] = seq.antecedent.filter(x => !x.formula.containsQuantifier).map(x => x.formula.asInstanceOf[FOLFormula]).toList
  // Propositional formulas on the right
  val prop_r : List[FOLFormula] = seq.succedent.filter(x => !x.formula.containsQuantifier).map(x => x.formula.asInstanceOf[FOLFormula]).toList
 
  val decomposition : (List[FOLTerm], List[FOLTerm]) = d
  val u = d._1
  val s = d._2
 
  // Instanciated (previously univ. quantified) formulas on the left
  val inst_l : List[FOLFormula] = u.foldRight(List[FOLFormula]()) { case (term, acc) =>
    val terms = flatterms.getTermTuple(term)
    val f = flatterms.getFormula(term)
    f.formula.asInstanceOf[FOLFormula] match {
      case AllVar(_, _) => f.formula.asInstanceOf[FOLFormula].substituteAll(terms) :: acc
      case _ => acc
    }
  }
  // Instanciated (previously ex. quantified) formulas on the right
  val inst_r : List[FOLFormula] = u.foldRight(List[FOLFormula]()) { case (term, acc) =>
    val terms = flatterms.getTermTuple(term)
    val f = flatterms.getFormula(term)
    f.formula.asInstanceOf[FOLFormula] match {
      case ExVar(_, _) => f.formula.asInstanceOf[FOLFormula].substituteAll(terms) :: acc
      case _ => acc
    }
  } 
 

  // Canonical solution  
  val alpha = FOLVar(new VariableStringSymbol("α"))
  val xvar = FOLVar(new VariableStringSymbol("x"))
    val xFormulas = u.foldRight(List[FOLFormula]()) { case (term, acc) =>
      val terms = flatterms.getTermTuple(term)
      val f = flatterms.getFormula(term)
      val xterms = terms.map(e => FOLSubstitution(e, alpha, xvar))
      f.formula.asInstanceOf[FOLFormula].substituteAll(xterms) :: acc
    }

  val canonicalSol : FOLFormula = AllVar(xvar, andN(xFormulas))
 
  // For printing Xα -> ^ Xsi (not used for practical purposes)
  //val x = ConstantStringSymbol("X")
  //val alpha = FOLVar(new VariableStringSymbol("α"))
  //val xalpha = Atom(x, alpha::Nil)
  // X[s_i] forall i
  //val xs = s.map(t => Atom(x, t::Nil))
  //val bigConj = andN(xs)
  // Implication parametrized with second order variable X (is this needed except for printing purposes??)
  //val implication : FOLFormula = Imp(xalpha, bigConj)


  // Checks if the sequent is a tautology using f as the cut formula
  def isValidWith(f: FOLFormula) : Boolean = {

    val body = f.substitute(FOLVar(new VariableStringSymbol("α")))

    val as = decomposition._2.foldRight(List[FOLFormula]()) {case (t, acc) =>
      acc :+ f.substitute(t) 
    }
    val head = andN(as)

    val impl = Imp(body, head)

    val antecedent = this.prop_l ++ this.inst_l :+ impl
    val succedent = this.prop_r ++ this.inst_r

    solvePropositional(FSequent(antecedent, succedent)) match {
      case Some(proof) => true
      case None => false
    }
  }

}

