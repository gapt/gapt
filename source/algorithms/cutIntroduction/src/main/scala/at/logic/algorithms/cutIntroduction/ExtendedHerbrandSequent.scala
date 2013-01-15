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
// NOTE2: seq should be prenex and skolemized 
class ExtendedHerbrandSequent(seq: Sequent, g: Grammar, cf: FOLFormula = null) {
 
  val endSequent = seq
  val flatterms = g.flatterms
  val grammar = g

  // From ".map" on are lots of castings just to make the data structure right :-|
  // FormulaOccurrence to HOLFormula to FOLFormula and Seq to List...
  
  // Propositional formulas on the left
  private val prop_l : List[FOLFormula] = seq.antecedent.filter(x => !x.formula.containsQuantifier).map(x => x.formula.asInstanceOf[FOLFormula]).toList
  // Propositional formulas on the right
  private val prop_r : List[FOLFormula] = seq.succedent.filter(x => !x.formula.containsQuantifier).map(x => x.formula.asInstanceOf[FOLFormula]).toList
  
  // Instanciated (previously univ. quantified) formulas on the left
  private val inst_l : List[FOLFormula] = grammar.u.foldRight(List[FOLFormula]()) { case (term, acc) =>
    val terms = flatterms.getTermTuple(term)
    val f = flatterms.getFormula(term)
    f.formula.asInstanceOf[FOLFormula] match {
      case AllVar(_, _) => f.formula.asInstanceOf[FOLFormula].substituteAll(terms) :: acc
      case _ => acc
    }
  }
  // Instanciated (previously ex. quantified) formulas on the right
  private val inst_r : List[FOLFormula] = grammar.u.foldRight(List[FOLFormula]()) { case (term, acc) =>
    val terms = flatterms.getTermTuple(term)
    val f = flatterms.getFormula(term)
    f.formula.asInstanceOf[FOLFormula] match {
      case ExVar(_, _) => f.formula.asInstanceOf[FOLFormula].substituteAll(terms) :: acc
      case _ => acc
    }
  }

  // Separating the formulas that contain or not the eigenvariable
  val antecedent = prop_l ++ inst_l.filter(f => !f.getFreeAndBoundVariables._1.contains(g.eigenvariable))
  val antecedent_alpha = inst_l.filter(f => f.getFreeAndBoundVariables._1.contains(g.eigenvariable))
  val succedent = prop_r ++ inst_r.filter(f => !f.getFreeAndBoundVariables._1.contains(g.eigenvariable))
  val succedent_alpha = inst_r.filter(f => f.getFreeAndBoundVariables._1.contains(g.eigenvariable))

  var cutFormula = if(cf == null) CutIntroduction.computeCanonicalSolution(seq, g) else cf

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

    val body = f.substitute(grammar.eigenvariable)

    val as = grammar.s.foldRight(List[FOLFormula]()) {case (t, acc) =>
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

  // The canonical solution computed already has only the quantified formulas 
  // from the end-sequent (propositional part is ignored).
  //
  // returns the list of improved solutions found by the forgetful resolution
  // algorithm.
  private def improveSolution : List[FOLFormula] = {

    // Remove quantifier 
    val (x, f) = cutFormula match {
      case AllVar(x, form) => (x, form)
      case _ => throw new CutIntroException("ERROR: Canonical solution is not quantified.")
    }

    // Transform to conjunctive normal form
    val cnf = f.toCNF

    // Exhaustive search over the resolvents (depth-first search),
    // returns the list of all solutions found.
    def searchSolution(f: FOLFormula) : List[FOLFormula] =
      f :: CutIntroduction.ForgetfulResolve(f).foldRight(List[FOLFormula]()) ( (r, acc) => 
          if(this.isValidWith(AllVar(x,r))) {
            searchSolution(r) ::: acc
          }
          else {
            acc 
          }
        )

    searchSolution(cnf).map(s => AllVar(x, s))
  }

  def minimizeSolution = {
    val minimalSol = this.improveSolution.sortWith((r1,r2) => r1.numOfAtoms < r2.numOfAtoms).head
    this.cutFormula = minimalSol
  }
}

