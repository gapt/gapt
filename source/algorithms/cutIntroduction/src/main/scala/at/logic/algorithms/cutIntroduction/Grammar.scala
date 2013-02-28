/*
 * Grammar that generates a list of terms T
 * 
 * NOTE: This is not the implementation of a grammar in the usual sense.
 * Here we keep only two sets, U and S, for the grammar with start symbol 'τ',
 * non-terminal 'α' and production rules 
 * P = { τ -> u | u in U} union { α -> s | s in S } 
 */

package at.logic.algorithms.cutIntroduction

import at.logic.language.lambda.symbols._
import at.logic.language.fol._
import at.logic.calculi.occurrences._
import scala.collection.mutable._
import at.logic.language.hol.logicSymbols._
import at.logic.utils.dssupport.ListSupport._
import at.logic.utils.dssupport.MapSupport._
import at.logic.utils.logging.Logger

class Grammar(u0: List[FOLTerm], s0: List[FOLTerm], ev: FOLVar) {

  val u = u0
  val s = s0
  val eigenvariable = ev

  // Is this the best solution?
  var flatterms: FlatTermSet = null

  def size = u.size + s.size

  def strictSuperGrammarOf(g : Grammar) = 
    // U o S \supset U' o S'
    // U \supset U' and S \supset S'
    g.u.forall(e => u.contains(e)) && g.s.forall(e => s.contains(e)) &&
    // |U| > |U'| or |S| > |S'|
    (u.size > g.u.size || s.size > g.s.size)

  def strictLeftSuperGrammarOf( g : Grammar ) = 
    g.u.forall(e => u.contains(e)) && g.s.forall(e => s.contains(e)) &&
    u.size > g.u.size

  def strictRightSuperGrammarOf( g : Grammar ) =
    g.u.forall(e => u.contains(e)) && g.s.forall(e => s.contains(e)) &&
    s.size > g.s.size

  def toPrettyString = "{ " + u.foldRight("")((ui, str) => str + ui + ", ") + " } o { " + s.foldRight("") ((si, str) => str + si + ", " ) + " }" 

}

object ComputeGrammars extends Logger {

  // This looks ugly :(
  def apply(terms: FlatTermSet) : List[Grammar] = apply(terms.termset).map{ case g => g.flatterms = terms; g }

  def apply(terms: List[FOLTerm]) : List[Grammar] = {
    // TODO: when iterating for the case of multiple cuts, change this variable.
    val eigenvariable = FOLVar(new VariableStringSymbol("α"))
    
    debug( "computing delta-table" )
    val deltatable = new DeltaTable(terms, eigenvariable)

    debug( "reading off grammars from delta-table" )
    findValidGrammars(terms, deltatable, eigenvariable).sortWith((g1, g2) =>
      g1.size < g2.size
    )
    
  }
  
  def findValidGrammars(terms: List[FOLTerm], deltatable: DeltaTable, ev: FOLVar) : List[Grammar] = {

    deltatable.table.foldRight(List[Grammar]()) {case ((s, pairs), grammars) =>
      // Ignoring entries where s.size == 1 because they are trivial
      // grammars with the function symbol on the right.
      if(s.size != 1) {

        // Add the trivial decomposition {alpha} o s
        var newpairs = pairs
        if(s.forall(e => terms.contains(e)) ) {
          newpairs = (ev, s) :: pairs
        }

        // Collect all possible subsets
        val allsubsets = subsets(newpairs)
       
        // For each subset, get the set U formed by the u_i's and the set T of the
        // terms covered (union of t_i)
        val subsetpairs = allsubsets.foldRight(List[(List[FOLTerm], List[FOLTerm])]()) {(subset, acc1) =>
          val d = subset.foldRight(List[FOLTerm](), List[FOLTerm]()) ( (el, acc2) => el._1 match {
            case null => acc2
            case _ => (el._1 :: acc2._1, el._2 ++ acc2._2)
          })
          d :: acc1
        }
       
        // Generate valid grammars
        // Note: each pair is ({u_1, ..., u_k}, {t_1, ..., t_j}) and for this to
        // be a valid decomposition, {t_1, ..., t_j} must contain all terms or
        // adding the missing terms to U should not exceed the size of the term
        // set.
        val ssize = s.size
        subsetpairs.foldRight(grammars) {
          case (p, acc) =>
            val termsCovered = p._2
            val difference = terms.diff(termsCovered)
       
            // The grammar generates all the terms
            if(difference.size == 0) {
              (new Grammar(p._1, s, ev)) :: acc
            }
            // Some constants are added to U and this is still reasonably small
            else if(p._1.size + difference.size + ssize < terms.size) {
              (new Grammar(p._1 ++ difference, s, ev)) :: acc
            }
            // No good
            else acc
        }
      }
      else grammars
    }
  }
}
