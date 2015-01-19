/*
 *  Extended Herbrand Sequent implementation
 *
 *  For more details on what this is, see: Towards Algorithmic Cut Introduction
 *  (S. Hetzl, A. Leitsch, D. Weller - LPAR-18, 2012)
 *
 */

package at.logic.algorithms.cutIntroduction

import at.logic.calculi.occurrences._
import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.language.fol._
import at.logic.algorithms.resolution._
import at.logic.calculi.resolution.FClause
import scala.collection.immutable.Stack
import at.logic.algorithms.cutIntroduction.MinimizeSolution.MyFClause
import at.logic.utils.dssupport.ListSupport.mapAccumL
import at.logic.utils.executionModels.searchAlgorithms.SearchAlgorithms.DFS
import at.logic.utils.executionModels.searchAlgorithms.SearchAlgorithms.setSearch
import at.logic.utils.executionModels.searchAlgorithms.SetNode
import at.logic.provers.minisat.MiniSAT


// NOTE: implemented for the one cut case.
// NOTE2: seq should be prenex and skolemized 
class ExtendedHerbrandSequent(seq: Sequent, g: Grammar, cf: FOLFormula = null) {
 
  val endSequent = seq
  val terms = g.terms
  val grammar = g

  // From ".map" on are lots of castings just to make the data structure right :-|
  // FormulaOccurrence to HOLFormula to FOLFormula and Seq to List...
  
  // Propositional formulas on the left
  val prop_l : List[FOLFormula] = seq.antecedent.filter(x => !containsQuantifier(x.formula.asInstanceOf[FOLFormula])).map(x => x.formula.asInstanceOf[FOLFormula]).toList
  // Propositional formulas on the right
  val prop_r : List[FOLFormula] = seq.succedent.filter(x => !containsQuantifier(x.formula.asInstanceOf[FOLFormula])).map(x => x.formula.asInstanceOf[FOLFormula]).toList
  
  // Instanciated (previously univ. quantified) formulas on the left
  val inst_l : List[FOLFormula] = grammar.u.foldRight(List[FOLFormula]()) { case (term, acc) =>
    val set = terms.getTermTuple(term)
    val f = terms.getFormula(term)
    f match {
      case AllVar(_, _) => instantiateAll(f, set) :: acc
      case _ => acc
    }
  }
  // Instantiated (previously ex. quantified) formulas on the right
  val inst_r : List[FOLFormula] = grammar.u.foldRight(List[FOLFormula]()) { case (term, acc) =>
    val set = terms.getTermTuple(term)
    val f = terms.getFormula(term)
    f match {
      case ExVar(_, _) => instantiateAll(f, set) :: acc
      case _ => acc
    }
  }

  // Separating the formulas that contain/don't contain eigenvariables
  def varFree(f : FOLFormula) = freeVariables(f).intersect(g.eigenvariables).isEmpty
  val antecedent = prop_l ++ inst_l.filter(varFree)
  val antecedent_alpha = inst_l.filter(x => !varFree(x))
  val succedent = prop_r ++ inst_r.filter(varFree)
  val succedent_alpha = inst_r.filter(x => !varFree(x))

  var cutFormula = if(cf == null) CutIntroduction.computeCanonicalSolution(seq, g) else cf

  override def toString = {

    // For printing Xα -> ^ Xsi
    /*val X = ConstantStringSymbol("X")
    val alpha = FOLVar(new VariableStringSymbol("α"))
    val xalpha = Atom(X, alpha::Nil)
    // X[s_i] forall i
    val xs = grammar.s.map(t => Atom("X", t::Nil))
    val bigConj = And(xs)
    // Implication parametrized with second order variable X (is this needed except for printing purposes??)
    val implication : FOLFormula = Imp(xalpha, bigConj)

    val str0 = antecedent_alpha.foldRight("") ( (f, acc) => acc + f + ", ")
    val str1 = antecedent.foldRight("") ( (f, acc) => acc + f + ", ")
    val str2 = succedent_alpha.foldRight("") ( (f, acc) => acc + f + ", ")
    val str3 = succedent.foldRight("") ( (f, acc) => acc + f + ", ")
    val str4 = cutFormula match { case AllVar( x, f ) => "λ " + x + ". " + f }
      
    (str1 + str0 + implication + " :- " + str3 + str2 + " where " + X + " = " + str4)*/

    ""
  }
}
