/*
 * Implements the Delta Table used to store and find valid decompositions of a
 * term set.
 *
 * Implements the delta-different of a set of terms 
 * (E.g.: delta(f(a), f(b)) = [f(alpha)], [a, b]
 * 
 * */
 
package at.logic.algorithms.cutIntroduction

import at.logic.language.fol._
import at.logic.calculi.occurrences._
import scala.collection.mutable._
import at.logic.utils.dssupport.ListSupport._
import at.logic.utils.dssupport.MapSupport._

class DeltaTableException(msg: String) extends Exception(msg)

class DeltaTable(terms: List[FOLTerm], eigenvariable: FOLVar) {
   
  var table = new HashMap[List[FOLTerm], List[(FOLTerm, List[FOLTerm])]] 

  // Fills the delta table with some terms

  // Initialize with empty decomposition
  add(Nil, null, Nil)

  for (n <- 1 until terms.length+1) {
    // Take only the decompositions of term sets of size (n-1) from the current delta table
    val one_less = getDecompositionsOfSize(n-1)

    one_less.foreach { case (s, pairs) =>

      // Iterate over the list of decompositions
      pairs.foreach { case (u, ti) =>
        // Only choose terms that are after the last term in tl
        val maxIdx = terms.lastIndexWhere(e => ti.contains(e))
        val termsToAdd = terms.slice(maxIdx + 1, (terms.size + 1))

        // Compute delta of the incremented list
        termsToAdd.foreach {case e =>
          val incrementedtermset = ti :+ e
          val p = delta(incrementedtermset, eigenvariable)

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
          if (p._2.size == 1 || p._2 != (incrementedtermset)) {
            // Update delta-table
            add(p._2, p._1, incrementedtermset)
          }
        }

      }
    }
  }

  def add(s: List[FOLTerm], u: FOLTerm, t: List[FOLTerm]) {
 
    if(table.contains(s)) {
      table(s) = table(s) :+ (u, t)
    }
    else {
      table(s) = ((u, t)::Nil)
    }
  }

  def get(s: List[FOLTerm]) = table(s)
 
  def getDecompositionsOfSize(n: Int) = {
    table.filter( e => e._1.length == n)
  }
}

object delta {
  // There must be a better way...
  // TODO: this should go somewhere else?
  def listEquals(lst1: List[FOLTerm], lst2: List[FOLTerm]) : Boolean = (lst1, lst2) match {
    case (Nil, Nil) => true
    case (hd1::tl1, hd2::tl2) => (hd1 =^ hd2) && listEquals(tl1, tl2)
    case (_, _) => false
  }
 
  // Delta difference
  def apply(terms: List[FOLTerm], eigenvariable: FOLVar) : (FOLTerm, List[FOLTerm]) = terms.size match {
    // IMPORTANT!!!!
    // With this, the constant decomposition is not found. Without this, the constant decomposition is the only one found.
    case 1 => return (eigenvariable, terms)
    case _ => terms.head match {
      // If the variables are reached
      case FOLVar(s) =>
        // If all variables are equal
        if ( terms.forall(t => t =^ terms.head) ) { return (FOLVar(s), Nil) }
        // If there are different variables 
        else { return (eigenvariable, terms) }
 
      // If the terms are functions
      case Function(h, args) =>
        // If all heads are the same
        if ( terms.forall(t => t match {
          case Function(h1, _) if h1 == h => true
          case _ => false
        }) ) {
          // call delta recursively for every argument of every term
 
          // Compute a list of list of arguments
          val allargs = terms.foldRight(List[List[FOLTerm]]()) ( (t, acc) => t match {
              case Function(x, args) => args :: acc
              case _ => throw new DeltaTableException("ERROR: Mal-formed terms list.")
            })
 
          // The list above is a list of lists of arguments. Assume that each list
          // of arguments has elements from 1 to n. A function should be called
          // for a list of all elements in position i. If this was a matrix, this 
          // is a function on the column of the matrix.
          // By computing the transpose of this matrix, the columns are now the 
          // rows, i.e., the inner lists. So we can just use fold to apply the
          // function to every such list.
          val listOfArgs = transpose(allargs)
          val deltaOfArgs = listOfArgs.foldRight(List[(FOLTerm, List[FOLTerm])]()) ((a, acc) => delta(a, eigenvariable) :: acc)
         
          // A delta vector can be constructed only if the lists returned from the arguments are all the same
          
          // Get all non-empty sets of terms returned (we don't care about the empty ones).
          val nonempty = deltaOfArgs.foldRight(List[List[FOLTerm]]()) ((x, acc) => x._2 match {
            case Nil => acc
            case t => t :: acc
          })
 
          // If all the sets are empty
          if (nonempty.length == 0) {
            val newargs = deltaOfArgs.foldRight(List[FOLTerm]()) ((x, acc) => x._1 :: acc)
            val u = Function(h, newargs)
            (u, Nil) 
          }
          else {
            // Check if they are the same
            val first = nonempty.head
            if (nonempty.forall(l => listEquals(l, first))) {
              // All terms are the same
              val newargs = deltaOfArgs.foldRight(List[FOLTerm]()) ((x, acc) => x._1 :: acc)
              val u = Function(h, newargs)
              (u, first)
            }
            // The terms returned from the arguments are different
            else {
              return (eigenvariable, terms)
            }
          }
        }
        // If head terms are different
        else { return (eigenvariable, terms) }
    }
  }
}
