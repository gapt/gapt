/**
 * Decomposition computation
 * 
 *
 */

package at.logic.algorithms.cutIntroduction

import at.logic.language.lambda.symbols._
import at.logic.language.fol._
import scala.collection.mutable._

class DecompositionException(msg: String) extends Exception(msg)

object decomposition {

  // Input: a set of terms
  // Output: two sets of terms
//  def apply(terms: List[Seq[FOLExpression]]) : (List[FOLTerm],List[FOLTerm]) = {
//    val lst = terms.flatten
//    val deltatable = computeDeltaTable(lst)
//  }

//  private def computeDeltaTable(terms: List[FOLTerm]) = {
    // This HashMap is mutable because I will update it frequently and do not want a new one returned...
//    val deltaTbl = new HashMap[List[FOLTerm], List[FOLTerm, List[FOLTerm]]]
    // Adds ti : (alpha, ti) to the table
//    terms.foreach(t => deltaTbl + (t -> ((FOLVar("alpha", i), t::Nil)::Nil)))
//  }

  def delta(terms: List[FOLTerm]) : (FOLTerm, List[FOLTerm]) = terms.head match {
    // If the variables are reached
    case FOLVar(s) =>
      // If all variables are equal
      if ( terms.forall(t => t =^ terms.head) ) { return (FOLVar(s), Nil) }
      // If there are different variables 
      else { return (FOLVar(new VariableStringSymbol("alpha")), terms) }

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
            case _ => throw new DecompositionException("Mal-formed terms list.")
          })

        // The list above is a list of lists of arguments. Assume that each list
        // of arguments has elements from 1 to n. A function should be called
        // for a list containing all elements in position i in every list. In
        // order to do this, this function will invert this list of lists. If
        // the list of lists was implemented with a matrix, all I had to do
        // would be to call the function on the columns of the matrix, but since
        // this is not the case I implemented this inverse function. 
        def inverse(args: List[List[FOLTerm]]) : List[List[FOLTerm]] = args match {
          case Nil => Nil
          case (Nil) :: tl => Nil
          case hd :: tl => 
            val heads = args.foldRight(List[FOLTerm]()) ( (lst, acc) => lst.head :: acc )
            val tails = args.foldRight(List[List[FOLTerm]]()) ( (lst, acc) => lst.tail :: acc )
            heads::inverse(tails)             
        }

        val listOfArgs = inverse(allargs)
        val deltaOfArgs = listOfArgs.foldRight(List[(FOLTerm, List[FOLTerm])]()) ((a, acc) => delta(a) :: acc)
       
        // A delta vector can be constructed only if the lists returned from the arguments are all the same
        
        // Get all non-empty sets of terms returned (we don't care about the empty ones).
        val nonempty = deltaOfArgs.foldRight(List[List[FOLTerm]]()) ((x, acc) => x._2 match {
          case Nil => acc
          case t => t :: acc
        })

        // There must be a better way...
        def listEquals(lst1: List[FOLTerm], lst2: List[FOLTerm]) : Boolean = (lst1, lst2) match {
          case (Nil, Nil) => true
          case (hd1::tl1, hd2::tl2) => (hd1 =^ hd2) && listEquals(tl1, tl2)
          case (_, _) => false
        }

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
            return (FOLVar(new VariableStringSymbol("alpha")), terms)
          }
        }
      }
      // If head terms are different
      else { return (FOLVar(new VariableStringSymbol("alpha")), terms) }
  }
  
}

