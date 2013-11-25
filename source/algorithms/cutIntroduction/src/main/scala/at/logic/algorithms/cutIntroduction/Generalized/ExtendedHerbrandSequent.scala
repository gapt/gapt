/*
 *  Extended Herbrand Sequent implementation
 *
 *  For more details on what this is, see: Towards Algorithmic Cut Introduction
 *  (S. Hetzl, A. Leitsch, D. Weller - LPAR-18, 2012)
 *
 */

package at.logic.algorithms.cutIntroduction.Generalized

import at.logic.calculi.occurrences._
import at.logic.calculi.lk.base._
import at.logic.calculi.lk.propositionalRules._
import at.logic.calculi.lk.quantificationRules._
import at.logic.language.fol._
import at.logic.language.fol.Utils._
import at.logic.algorithms.lk.solvePropositional._
import at.logic.language.lambda.symbols._
import at.logic.language.hol.logicSymbols._
import at.logic.algorithms.resolution._
import at.logic.calculi.resolution.base.FClause
import at.logic.utils.logging.Logger
import scala.collection.immutable.Stack
import at.logic.algorithms.cutIntroduction.MinimizeSolution.MyFClause
import at.logic.utils.dssupport.ListSupport.mapAccumL
import at.logic.utils.executionModels.searchAlgorithms.SearchAlgorithms.DFS
import at.logic.utils.executionModels.searchAlgorithms.SearchAlgorithms.setSearch
import at.logic.utils.executionModels.searchAlgorithms.SetNode
import at.logic.provers.minisat.MiniSAT
import at.logic.algorithms.cutIntroduction.{Grammar => BaseGrammar, ExtendedHerbrandSequent => BaseExtendedHerbrandSequent,
                                            CutIntroduction => BaseCutIntroduction, DeltaTable => BaseDeltaTable,
                                            DefaultProver, CutIntroUncompressibleException, CutIntroEHSUnprovableException,
                                            CutIntroException, TermsExtraction, FlatTermSet, DeltaTableException}


// NOTE: implemented for the one cut case.
// NOTE2: seq should be prenex and skolemized 
class ExtendedHerbrandSequent(seq: Sequent, g: Grammar, cf: FOLFormula = null) extends Logger {
 
  val endSequent = seq
  val flatterms = g.flatterms
  val grammar = g

  // From ".map" on are lots of castings just to make the data structure right :-|
  // FormulaOccurrence to HOLFormula to FOLFormula and Seq to List...
  
  // Propositional formulas on the left
  val prop_l : List[FOLFormula] = seq.antecedent.filter(x => !x.formula.containsQuantifier).map(x => x.formula.asInstanceOf[FOLFormula]).toList
  // Propositional formulas on the right
  val prop_r : List[FOLFormula] = seq.succedent.filter(x => !x.formula.containsQuantifier).map(x => x.formula.asInstanceOf[FOLFormula]).toList
  
  // Instanciated (previously univ. quantified) formulas on the left
  val inst_l : List[FOLFormula] = grammar.u.foldRight(List[FOLFormula]()) { case (term, acc) =>
    val terms = flatterms.getTermTuple(term)
    val f = flatterms.getFormula(term)
    f match {
      case AllVar(_, _) => f.instantiateAll(terms) :: acc
      case _ => acc
    }
  }
  // Instantiated (previously ex. quantified) formulas on the right
  val inst_r : List[FOLFormula] = grammar.u.foldRight(List[FOLFormula]()) { case (term, acc) =>
    val terms = flatterms.getTermTuple(term)
    val f = flatterms.getFormula(term)
    f match {
      case ExVar(_, _) => f.instantiateAll(terms) :: acc
      case _ => acc
    }
  }

  // Separating the formulas that contain/don't contain eigenvariables
  def varFree(f : FOLFormula) = f.freeVariables.intersect(g.eigenvariables.toSet).isEmpty
  val antecedent = prop_l ++ inst_l.filter(varFree)
  val antecedent_alpha = inst_l.filter(x => !varFree(x))
  val succedent = prop_r ++ inst_r.filter(varFree)
  val succedent_alpha = inst_r.filter(x => !varFree(x))

  //trace("antecent: " + prop_l + " ++ " + inst_l.filter(varFree))
  //trace("antecent_alpha: " + inst_l.filter(x => !varFree(x)))
  //trace("succedent: " + prop_r + " ++ " + inst_r.filter(varFree))
  //trace("succedent_alpha: " + inst_r.filter(x => !varFree(x)))

  var cutFormula = if(cf == null) CutIntroduction.computeCanonicalSolution(seq, g) else cf

  override def toString = {

    // For printing Xα -> ^ Xsi
    /*val X = ConstantStringSymbol("X")
    val alpha = FOLVar(new VariableStringSymbol("α"))
    val xalpha = Atom(X, alpha::Nil)
    // X[s_i] forall i
    val xs = grammar.s.map(t => Atom(X, t::Nil))
    val bigConj = andN(xs)
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

  /** Checks if the sequent is a tautology using f as the cut formula.
    * 
    * @param sat A SAT-solver that performs the validity check.
    * @param f The formula to be checked. It will be instantiated with the
    *          eigenvariable of the solution's grammar.
    *          For details, see introqcuts.pdf, Chapter 5, Prop. 4, Example 6.
    * @return True iff f still represents a valid solution.
    */
  def isValidWith(sat: MiniSAT, f: FOLFormula) : Boolean = {

    //Instantiate with the eigenvariables.
    val body = grammar.eigenvariables.foldLeft(f)((f,ev) => f.instantiate(ev))

    //Instantiate with all the values in s.
    val as = grammar.s.transpose.foldLeft(List[FOLFormula]()) {case (acc, t) =>
      (t.foldLeft(f){case (f, sval) => f.instantiate(sval)}) :: acc
    }

    val head = andN(as)

    val impl = Imp(body, head)

    val antecedent = this.prop_l ++ this.inst_l :+ impl
    val succedent = this.prop_r ++ this.inst_r

    //isTautology(FSequent(antecedent, succedent))
    //trace( "calling SAT-solver" )
    val r = sat.isValid(Imp(andN(antecedent), orN(succedent)))
    //trace( "finished call to SAT-solver" )

    r
  }

  // The canonical solution computed already has only the quantified formulas 
  // from the end-sequent (propositional part is ignored).
  //
  // returns the list of improved solutions found by the forgetful resolution
  // algorithm.
  private def improveSolution : List[FOLFormula] = {

    val sat = new MiniSAT()

    val (xs, f) = removeQuantifiers(cutFormula)

    if (xs.length == 0) { throw new CutIntroException("ERROR: Canonical solution is not quantified.") }

    // Transform to conjunctive normal form
    val cnf = f.toCNF

    // Exhaustive search over the resolvents (depth-first search),
    // returns the list of all solutions found.
    var count = 0

    def searchSolution(f: FOLFormula) : List[FOLFormula] =
      f :: MinimizeSolution.ForgetfulResolve(f).foldLeft(List[FOLFormula]()) ( (acc, r) =>
          //Re-quantify the resolved f and checker whether it's still a tautology.
          //If so, keep applying resolution to it and add the results to acc.
          if( this.isValidWith(sat, addQuantifiers(r, xs))) {
            //trace( "found solution with " + r.numOfAtoms + " atoms: " + r )
            count = count + 1
            searchSolution(r) ::: acc
          }
          else {
            count = count + 1
            acc 
          }
        )

    val res = searchSolution(cnf).map(s => addQuantifiers(s,xs))

    //debug("IMPROVESOLUTION - # of sets examined: " + count + ". finished.")
    res
  }

  def minimizeSolution = {
    //trace( "minimizing solution " + cutFormula )
    val minimalSol = this.improveSolution.sortWith((r1,r2) => r1.numOfAtoms < r2.numOfAtoms).head
    this.cutFormula = minimalSol
  }

  /*def minimizeSolution2 = {
    //trace( "minimizing solution " + cutFormula )
    val minimalSol = this.improveSolution2.sortWith((r1,r2) => r1.numOfAtoms < r2.numOfAtoms).head
    this.cutFormula = minimalSol
  }*/
}
