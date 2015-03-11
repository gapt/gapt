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
class ExtendedHerbrandSequent( val endSequent: FSequent, val grammar: MultiGrammar, cf: List[FOLFormula] = Nil ) {
  // TODO: do we even want to allow cf == Nil?
  val cutFormulas = if ( cf == Nil ) CutIntroduction.computeCanonicalSolutions( grammar ) else cf

  // From ".map" on are lots of castings just to make the data structure right :-|
  // FormulaOccurrence to HOLFormula to FOLFormula and Seq to List...

  // Propositional formulas on the left
  val prop_l: List[FOLFormula] = endSequent.antecedent.filter( x => !containsQuantifier( x.asInstanceOf[FOLFormula] ) ).map( x => x.asInstanceOf[FOLFormula] ).toList
  // Propositional formulas on the right
  val prop_r: List[FOLFormula] = endSequent.succedent.filter( x => !containsQuantifier( x.asInstanceOf[FOLFormula] ) ).map( x => x.asInstanceOf[FOLFormula] ).toList
  //Quantified formulas on the left
  val quant_l: List[FOLFormula] = endSequent.antecedent.filter( x => containsQuantifier( x.asInstanceOf[FOLFormula] ) ).map( x => x.asInstanceOf[FOLFormula] ).toList
  //Quantified formulas on the right
  val quant_r: List[FOLFormula] = endSequent.succedent.filter( x => containsQuantifier( x.asInstanceOf[FOLFormula] ) ).map( x => x.asInstanceOf[FOLFormula] ).toList

  // Instantiated (previously univ. quantified) formulas on the left
  val inst_l: List[FOLFormula] = grammar.us.keys.foldRight( List[FOLFormula]() ) {
    case ( f, acc ) =>
      f match {
        case AllVar( _, _ ) => instantiateAll( f, grammar.us( f ) ).toList ++ acc
        case _              => acc
      }
  }
  // Instantiated (previously ex. quantified) formulas on the right
  val inst_r: List[FOLFormula] = grammar.us.keys.foldRight( List[FOLFormula]() ) {
    case ( f, acc ) =>
      f match {
        case ExVar( _, _ ) => instantiateAll( f, grammar.us( f )  ).toList ++ acc
        case _             => acc
      }
  }

  // Separating the formulas that contain/don't contain eigenvariables
  def varFree( f: FOLFormula ) = freeVariables( f ).intersect( grammar.eigenvariables ).isEmpty
  val antecedent = prop_l ++ inst_l.filter( varFree )
  val antecedent_alpha = inst_l.filter( x => !varFree( x ) )
  val succedent = prop_r ++ inst_r.filter( varFree )
  val succedent_alpha = inst_r.filter( x => !varFree( x ) )


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

    antecedent.mkString( "", ", ", "" ) + ", " + antecedent_alpha.mkString( "", ", ", "" ) + " ⊦ " + succedent.mkString( "", ", ", "" ) + ", " + succedent_alpha.mkString( "", ", ", "" )
  }
}
