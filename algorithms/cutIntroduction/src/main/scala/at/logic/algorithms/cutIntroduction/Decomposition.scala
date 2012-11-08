/*
 * Computes a decomposition for a list of terms T
 * 
 */

package at.logic.algorithms.cutIntroduction

import at.logic.language.lambda.symbols._
import at.logic.language.fol._
import at.logic.calculi.occurrences._
import scala.collection.mutable._
import at.logic.language.hol.logicSymbols._
import at.logic.utils.dssupport.ListSupport._
import at.logic.utils.dssupport.MapSupport._

class DecompositionException(msg: String) extends Exception(msg)

object Decomposition {

  // Input: a hashmap of formulas pointing to a list of tuples of terms
  // Output: a list of decompositions for each formula.
  def apply(terms: List[FOLTerm]) : List[(List[FOLTerm], List[FOLTerm])] = {

    // TODO: when iterating for the case of multiple cuts, change this variable.
    val eigenvariable = FOLVar(new VariableStringSymbol("α"))
    
    val deltatable = new DeltaTable(terms, eigenvariable)

    //println("\n************The delta-table is: ")
    //deltatable.table.map {case (s, pairs) =>
    //  println("KEY: " + s)
    //  println("VALUES: " + pairs + "\n")
    //}
    
    findValidDecompositions(terms, deltatable, eigenvariable)
    
  }
  
  def findValidDecompositions(terms: List[FOLTerm], deltatable: DeltaTable, ev: FOLTerm) : List[(List[FOLTerm], List[FOLTerm])] = {

    deltatable.table.foldRight(List[(List[FOLTerm], List[FOLTerm])]()) {case ((s, pairs), decompositions) =>

      // Ignoring entries where s.size == 1 because they are trivial
      // decompositions with the function symbol on the right.
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
       
        // Generate valid decompositions
        // Note: each pair is ({u_1, ..., u_k}, {t_1, ..., t_j}) and for this to
        // be a valid decomposition, {t_1, ..., t_j} must contain all terms or
        // adding the missing terms to U should not exceed the size of the term
        // set.
        val ssize = s.size
        subsetpairs.foldRight(decompositions) {
          case (p, acc) =>
            val termsCovered = p._2
            val difference = terms.diff(termsCovered)
       
            // The decomposition covers all the terms
            if(difference.size == 0) {
              (p._1, s) :: acc
            }
            // Some constants are added to U and this is still reasonably small
            else if(p._1.size + difference.size + ssize < terms.size) {
              (p._1 ++ difference, s) :: acc
            }
            // No good
            else acc
        }
      }
      else decompositions
    }
  }
}

