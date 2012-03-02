/**
 * Decomposition computation
 * 
 *
 */

import at.logic.language.lambda.symbols._
import at.logic.language.fol._
import scala.collection.mutable._

package cutIntroduction {

class DecompositionException(msg: String) extends Exception(msg)

object decomposition {

  // Input: a set of terms
  // Output: two sets of terms
//  def apply(terms: List[Seq[FOLExpression]]) : (List[FOLTerm],List[FOLTerm]) = {
//    val lst = terms.flatten
//    val deltatable = computeDeltaTable(lst)
//  }

//  private def computeDeltaTable(terms: List[FOLTerm]) = {
    // TODO: check if the terms are well formed first
    // This HashMap is mutable because I will update it frequently and do not want a new one returned...
//    val deltaTbl = new HashMap[List[FOLTerm], List[FOLTerm, List[FOLTerm]]]
    // Adds ti : (alpha, ti) to the table
//    terms.foreach(t => deltaTbl + (t -> ((FOLVar("alpha", i), t::Nil)::Nil)))
//  }

  private def delta(terms: List[FOLTerm]) : (FOLTerm, List[FOLTerm]) = terms.head match {
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
        // Here's to hoping that it will match this h with the h above
        case Function(h, _) => true
        case _ => false
      }) ) {
        // call delta recursively for every argument of every term

        // Compute a list of list of arguments
        val allargs = terms.foldRight(List[List[FOLTerm]]()) ( (t, acc) => t match {
            case Function(x, args) => args :: acc
            case _ => throw new DecompositionException("Mal-formed terms list.")
          })

        // These two functions are used to "revert" the list of lists computed above.
        // I still think that there must be a better way of doing it.
        def f(args: List[List[FOLTerm]]) : List[FOLTerm] = args.head match {
          case Nil => Nil
          case hd :: tl => hd :: f(args.tail)
        }
        def g(args: List[List[FOLTerm]]) : List[List[FOLTerm]] = args match {
          case Nil => Nil
          case hd :: tl => 
            val a = f(args)
            val tails = args.foldRight(List[List[FOLTerm]]()) ((lst, acc) => lst match {
              case hd :: tl => tl :: acc
              case Nil => acc
            })
            a::g(tails)             
        }

        val listOfArgs = g(allargs)
        val deltaOfArgs = listOfArgs.foldRight(List[(FOLTerm, List[FOLTerm])]()) ((a, acc) => delta(a) :: acc)
       
        // A delta vector can be constructed only if the lists returned from the arguments are all the same
        
        // Get all non-empty sets of terms returned (we don't care about the empty ones).
        val nonempty = deltaOfArgs.foldRight(List[List[FOLTerm]]()) ((x, acc) => x._2 match {
          case Nil => acc
          case t => t :: acc
        })

        // This must be implemented somewhere else... But it's faster now if I do it here. Please let me know where it is so I can substitute this.
        def listEquals(lst1: List[FOLTerm], lst2: List[FOLTerm]) : Boolean = (lst1, lst2) match {
          case (Nil, Nil) => false
          case (hd1::tl1, hd2::tl2) => (hd1 =^ hd2) && listEquals(tl1, tl2)
          case (_, _) => false
        }

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
      // If head terms are different
      else { return (FOLVar(new VariableStringSymbol("alpha")), terms) }
  }
  
}

}
