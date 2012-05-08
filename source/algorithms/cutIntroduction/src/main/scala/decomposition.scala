/**
 * Decomposition computation
 * 
 *
 */

package at.logic.algorithms.cutIntroduction

import at.logic.language.lambda.symbols._
import at.logic.language.fol._
import scala.collection.Map
import scala.collection.mutable._
import scala.collection.mutable.HashMap

class DecompositionException(msg: String) extends Exception(msg)

object decomposition {

  // Input: a set of terms
  // Output: two sets of terms
  def apply(terms: List[List[FOLTerm]]) : List[(List[FOLTerm],List[FOLTerm])] = {
    // Note: for the case of one quantifier, each sequence on this list will have
    // only one term
    val lst = terms.foldRight(List[FOLTerm]()) ((s, acc) => s ++ acc)
    val deltatable = computeDeltaTable(lst)
    val decompositions = findValidDecompositions(lst, deltatable)
    decompositions
  }

  def findValidDecompositions(terms: List[FOLTerm], deltaTable: HashMap[List[FOLTerm], List[(FOLTerm, List[FOLTerm])]]) = {
    deltaTable.foldRight(List[(List[FOLTerm], List[FOLTerm])]()) {case ((key, value), decompositions) =>
      // (s_1, ..., s_n)
      val s = key
      // List of: (u_i, (t_1, ..., t_k))
      var pairs = value
      // The trivial decomposition might be needed now
      // E.g.: T = {a, fa, f^2a, f^3a}
      if (s.forall(t => terms.contains(t))) {
        pairs = pairs :+ (FOLVar(new VariableStringSymbol("alpha")), s)
      }

      // Find all subsets (could not find a built-in scala function)
      // TODO: this should be put somewhere else...
      // TODO: find a more efficient way to do this.
      def subsets[T](s : List[T]) : List[List[T]] = {
        if (s.size == 0) List(List()) 
        else { 
          val tailSubsets = subsets(s.tail); 
          tailSubsets ++ tailSubsets.map(s.head :: _) 
        }
      }

      // Checks if the union of a subset of pairs contains all the terms
      
      // Collect all subsets
      val allsubsets = subsets(pairs)

      // Join the pairs of each subset
      val subsetpairs = allsubsets.foldRight(List[(List[FOLTerm], List[FOLTerm])]()) {(subset, acc1) =>
        val d = subset.foldRight(List[FOLTerm](), List[FOLTerm]()) ( (el, acc2) => (el._1 :: acc2._1, el._2 ++ acc2._2))
        d :: acc1
      }

      // Check which pairs are a decomposition
      // Note: each pair is ({u_1, ..., u_k}, {t_1, ..., t_j})
      // and for this to be a valid decomposition, {t_1, ..., t_j}
      // must contain all terms.
      val valid = subsetpairs.filter(p => p._2.contains(terms))

      val dec = valid.foldRight(List[(List[FOLTerm], List[FOLTerm])]()) ( (p, acc) => (p._1, s) :: acc)
      dec ++ decompositions
    }
  }

  def computeDeltaTable(terms: List[FOLTerm]) = {

    // Takes a hashmap and an integer i and process all entries of the hashmap
    // s.t. the key has size i-1
    // Returns a new hashmap with the new entries
    // NOTE: iterate one data structure, update another
    def g(m: HashMap[List[FOLTerm], List[(FOLTerm, List[FOLTerm])]], i: Int) :
    HashMap[List[FOLTerm], List[(FOLTerm, List[FOLTerm])]] = 
    {
      // HashMap that will hold the new delta-vectors computed
      var newentries = new HashMap[List[FOLTerm], List[(FOLTerm, List[FOLTerm])]]
      // Take only the elements of size (i-1) from the current delta table
      val mi = m.filter( e => e._1.length == (i-1))

      mi.foreach { case (key, value) => 
        // Iterate over the list of decompositions
        value.foreach {case (u, tl) =>
          // Only choose terms that are after the last term in tl
          val maxIdx = terms.lastIndexWhere(e => tl.contains(e))
          val termsToAdd = terms.slice(maxIdx+1, (terms.length+1))

          // Compute delta of the incremented list
          termsToAdd.foreach {case e =>
            val p = delta(tl :+ e)

            // If non-trivial
            if (p._2 != (tl :+ e)) {
              // Update new entries
              if (newentries.contains(p._2)) {
                val lst = newentries(p._2)
                val newlst = lst :+ (p._1, tl :+ e)
                newentries -= p._2
                newentries += (p._2 -> newlst)
              }
              else {
                newentries += (p._2 -> ((p._1, tl :+ e)::Nil))
              }
            }
          }
        }
      }
      // Return the hashmap with the new information
      m ++ newentries
    }
 
    // Iterate over the size of the terms list.
    // f(i) returns the delta table complete until elements of size i
    def f(i: Int) : HashMap[List[FOLTerm], List[(FOLTerm, List[FOLTerm])]] = i match {
      // Initialize hashmap
      case 1 => 
        var deltaTbl = new HashMap[List[FOLTerm], List[(FOLTerm, List[FOLTerm])]]
        terms.foreach(t => deltaTbl += ((t::Nil) -> ((FOLVar(new VariableStringSymbol("alpha")), t::Nil)::Nil)))
        deltaTbl
      // Compute
      case n => g(f(n-1), n)
    }

    // Return the complete delta table
    f(terms.length)
  }

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

