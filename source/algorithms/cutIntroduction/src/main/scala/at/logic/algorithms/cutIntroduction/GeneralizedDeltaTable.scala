/*
 * Implements the Delta Table used to store and find valid decompositions (grammars) of a
 * term set.
 *
 * Implements the delta-different of a set of terms 
 * (E.g.: delta(f(a), f(b)) = [f(alpha)], [a, b]
 * 
 * */
 
package at.logic.algorithms.cutIntroduction

import at.logic.language.fol._
import at.logic.language.fol.Utils._
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.calculi.occurrences._
import scala.collection.immutable.HashMap
import at.logic.utils.dssupport.ListSupport._
import at.logic.utils.logging.Logger
import at.logic.algorithms.cutIntroduction.Deltas._

//package-global definitions
package object types {
  /** A term with variables */
  type U = FOLTerm
  /** The s-vector for a single variable in u */
  type SVector = List[FOLTerm]
  /** The list of s-vectors of a substitution */
  type S = List[SVector]
  /* A decomposition constisting u and S */
  type Decomposition = (U,S)
}

/** A generalized delta table whose rows contains the results
  * of Delta_G(...) instead of Delta(...).
  *
  * A generalized delta table contains decompositions for subsets of a termset and
  * one can extract grammars from it by simply iterating through its rows.
  *
  * For details, see "Algorithmic Introduction of Quantified Cuts (Hetzl et al 2013)"
  * and deltavector.tex/.pdf in the /doc-directory.
  *
  * @param terms The terms occurring in an LK proof.
  * @param eigenvariable The name of eigenvariable that should be introduced in the decompositions.
  */
class GeneralizedDeltaTable(terms: List[FOLTerm], eigenvariable: String, delta: DeltaVector) extends Logger {
  var termsAdded : Int = 0
   
  var table = new HashMap[types.S, List[(types.U, List[FOLTerm])]] 
  val trivialEv = FOLVar(new VariableStringSymbol(eigenvariable + "_0"))

  // Fills the delta table with some terms

  // Initialize with empty decomposition
  trace( "initializing generalized delta-table" )
  add(Nil, null, Nil)


  for (n <- 1 until terms.length+1) {
    trace( "adding simple grammars for " + n + " terms to generalized delta-table" )

    // Take only the simple grammars of term sets of size (n-1) from the current delta table
    // Filter the keys (S) according to size
    val one_less = table.filter( e => safeHead(e._1,Nil).length == n - 1)

    trace("_____________________________________________________")
    trace("DT contains " + table.size + " elements. Filtered to " + one_less.size)
    trace("previously (for n=" + (n-1) + "), " + termsAdded + "entries were added")
    trace("one_less (n=" + n + "): ")
    trace(one_less.toString())
    trace("_____________________________________________________")


    termsAdded = 0

    //Go through each the decompositions for each (n-1)-sized key and try to add terms.
    one_less.foreach { case (s, pairs) =>

      // Iterate over the list of decompositions
      pairs.foreach { case (u, ti) =>
        // Only choose terms that are after the last term in tl

        val maxIdx = terms.lastIndexWhere(e => ti.contains(e))
        val termsToAdd = terms.slice(maxIdx + 1, (terms.size + 1))

        trace("termsToAdd with n     = " + n)
        trace("                maxIdx= " + maxIdx)
        trace("                ti    = " + ti)
        trace("termsToAdd (" + termsToAdd.size + ": ")
        trace(termsToAdd.toString())

        // Compute delta of the incremented list
        termsToAdd.foreach {case e =>
          val incrementedtermset = ti :+ e
          val p = delta.computeDelta(incrementedtermset, eigenvariable)

          trace("---------------------------------------------------------")
          trace("Computed deltaG of " + incrementedtermset)
          trace("Result:")
          trace(p.toString())
          trace("---------------------------------------------------------")

          termsAdded = termsAdded + 1

          // If non-trivial or equal to 1 (for the term set of size
          // 1, the decomposition is always trivial and should be added)
          // NOTE:
          // When the delta algorithm 2 is applied to an
          // f_i-prefixed set of terms as computed in step 1 and T_i corresponds to
          // a formula with only a single quantifier then every subset of {
          // f_i(t_1),...,f_i(t_l) } of f_i(T_i) will have the non-trivial
          // decomposition f_i(\alpha) o (t_1,...,t_l). This will not happen if T_i
          // corresponds to a formula with more than one quantifier. Right now, it
          // is better to not worry about this and rather consider it a potential
          // for further improvement.
          p.foreach{ case(u,s) =>
            if (incrementedtermset.size == 1 || u != trivialEv) add(s, u, incrementedtermset)
          }
        }

      }
    }
  }








  /** Adds a decomposition (u,s), under the key s, to the delta table.
    * Specifically, s is the index and (u,T) is the key, where (u,S) is
    * a decomposition of T.
    * If the key already exists, (u,T) is appended the list of existing values */
  def add(s: types.S, u: types.U, t: List[FOLTerm]) {
    trace("-------------ADD:")
    trace("s: " + s)
    trace("t: " + t)
    trace("u: " + u)

    if(table.contains(s)) {
      val lst = table(s)
      table += (s -> ((u, t) :: lst) )
    }
    else {
      table += ( s -> ((u, t)::Nil) )
    }
  }

  def numberOfPairs = table.foldRight(0) { case ((k, lst), acc) => lst.size + acc }

  def minNumOfPairsPerLine = table.foldRight(Int.MaxValue) { case ((k, lst), acc) => acc.min( lst.size ) }

  def maxNumOfPairsPerLine = table.foldRight(0) { case ((k, lst), acc) => acc.max( lst.size ) }

  /**
   * compute and print statistics about this delta-table
   * @prln the function used for printing
   **/
  def printStats( prln:  String => Unit ) {
    prln( "number of lines: " + table.size )
    prln( "total number of pairs: " + numberOfPairs )
    prln( "avg. number of pairs / line: " + ( numberOfPairs.toFloat / table.size ) )
    prln( "min. number of pairs / line: " + minNumOfPairsPerLine )
    prln( "max. number of pairs / line: " + maxNumOfPairsPerLine )

    val linestats = table.foldRight( new HashMap[Int,Int]() ) {
      case ((k, lst), acc) => acc + ( lst.size -> ( acc.getOrElse( lst.size, 0 ) + 1 ) ) 
    }
    prln( "  k   number of lines with k pairs" )
    linestats.toSeq.sortBy( _._1 ).foreach{
      case ( k, num ) => prln( "% 3d".format(k) + "   " + num )
    }
  }

  /*
  def debug(msg: String) = {
    println("============== DEBUG: DeltaTable ===============")
    println("Where: " + msg)
    println("Number of lines in the table: " + size)
    println("Each line contains pairs.")
    println("Total number of pairs: " + numberOfPairs)
    println("================================================")
  }
  */
}
