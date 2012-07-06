/**
 * Decomposition computation
 * 
 *
 */

package at.logic.algorithms.cutIntroduction

import at.logic.language.lambda.symbols._
import at.logic.language.fol._
import at.logic.calculi.occurrences._
import scala.collection.mutable._
import at.logic.language.hol.logicSymbols._

class DecompositionException(msg: String) extends Exception(msg)

class DeltaTable() {
  
  var table = new HashMap[List[FOLTerm], HashMap[FormulaOccurrence, List[(FOLTerm, List[FOLTerm])]]] 

  def add(f: FormulaOccurrence, t: List[FOLTerm], s: List[FOLTerm], u: FOLTerm) {

    if(table.contains(s) && table(s).contains(f)) {
      table(s)(f) = table(s)(f) :+ (u, t)
    }
    else if (table.contains(s)){
      table(s)(f) = ((u, t)::Nil)
    }
    // So sad that this HashMap is not created with the line above...
    else {
      table(s) = new HashMap()
      table(s)(f) = ((u, t)::Nil)
    }  
  }

  def get(s: List[FOLTerm], f: FormulaOccurrence) = table(s)(f)

  def getDecompositionsOfSize(n: Int) = {
    table.filter( e => e._1.length == n)
  }

  def findValidDecompositions(terms: Map[FormulaOccurrence, List[FOLTerm]]) 
  : List[(Map[FormulaOccurrence, List[FOLTerm]], List[FOLTerm])] = {

    val allFormulas = terms.keys

    // TODO: the next two or three functions should really be somewhere else...

    // Find all subsets (could not find a built-in scala function)
    def subsets[T](s : List[T]) : List[List[T]] = {
      if (s.size == 0) List(List()) 
      else { 
        val tailSubsets = subsets(s.tail); 
        tailSubsets ++ tailSubsets.map(s.head :: _) 
      }
    }

    // Cartesian product of an arbitrary list of lists
    def product[T](l: List[List[T]]): List[List[T]] = l match {
      case Nil => List(Nil)
      case h :: t => for(eh <- h; et <- product(t)) yield eh :: et
    }

    // TODO: parametrize the types.
    def mapProduct(m: Map[FormulaOccurrence, List[List[FOLTerm]]]): List[Map[FormulaOccurrence, List[FOLTerm]]] = {
      val forms = m.keySet.toList
      forms match {
        case Nil => List(Map.empty)
        case h :: t => for(eh <- m(h); et <- mapProduct(m - (h))) yield et + (h -> eh)
      }
    }

    def findFormulaDecompositions(s: List[FOLTerm], f: FormulaOccurrence) = {
      var pairs = table(s)(f)
      val t = terms(f)

      // The trivial decomposition might be needed now
      // E.g.: T = {a, fa, f^2a, f^3a} is a case where the trivial decomposition is needed
      // Obs: if s.length == 1, it is already the trivial decomposition
      if (s.length > 1 && s.forall(e => t.contains(e))) {
        pairs = pairs :+ (FOLVar(new VariableStringSymbol("alpha")), s)
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
      val valid = subsetpairs.filter(p => 
        t.forall(e => p._2.contains(e))
      )

      // Return all the U sets
      valid.foldRight(List[List[FOLTerm]]()) ((p, acc) => p._1 :: acc)
    }

    table.foldRight(List[(Map[FormulaOccurrence, List[FOLTerm]], List[FOLTerm])]()) {case ((s, forms), decompositions) =>

      if(allFormulas.forall(f => forms.keySet.contains(f))) {
        val setsOfUi = forms.keys.foldRight(Map[FormulaOccurrence, List[List[FOLTerm]]]()) { (f, acc) =>
          acc + (f -> findFormulaDecompositions(s, f))
        }

        if(!setsOfUi.isEmpty) {
          val uSets = mapProduct(setsOfUi)
  
          val dec = uSets.foldRight(List[(Map[FormulaOccurrence, List[FOLTerm]], List[FOLTerm])]()) { (u, acc) =>
            (u, s) :: acc 
          }
          dec ++ decompositions
        }
        else decompositions
      }
      else decompositions
    }
  }

}

object decomposition {

  // Input: a hashmap of formulas pointing to a list of terms
  // Output: two lists of terms
  def apply(terms: Map[FormulaOccurrence, List[List[FOLTerm]]]) 
  : List[(Map[FormulaOccurrence, List[List[FOLTerm]]], List[FOLTerm])] = {
    
    val newterms = terms.foldRight(Map[FormulaOccurrence, List[FOLTerm]]()) {
      case ((f, tuples), newmap) => newmap + (f -> tuplesToTerms(tuples)) 
    }
    val deltatable = fillDeltaTable(newterms)
    

    val decompositions = deltatable.findValidDecompositions(newterms)
    
    // NOTE: there shouldn't be a tuple symbol on the second element.
    decompositions.foldRight(List[(Map[FormulaOccurrence, List[List[FOLTerm]]], List[FOLTerm])]()) {
      case ((m, lst), acc) => (m.map{ case (k, v) => (k, termsToTuples(v))}, lst) :: acc
    }
  }

  val tupleFunctionSymbol = ConstantStringSymbol("##")
  def tuplesToTerms(terms: List[List[FOLTerm]]) : List[FOLTerm] = {
    terms.foldRight(List[FOLTerm]()) { 
      case (t, acc) => Function(tupleFunctionSymbol, t) :: acc
    }
  }
  def termsToTuples(terms: List[FOLTerm]) : List[List[FOLTerm]] = {
    terms.foldRight(List[List[FOLTerm]]()) {
      case (t, acc) => t match {
        case Function(tupleFunctionSymbol, lst) => lst :: acc
        case _ => throw new DecompositionException("Tuple symbol not used.")
      }
    }
  }

  def fillDeltaTable(terms: Map[FormulaOccurrence, List[FOLTerm]]) = {

    var deltaTable = new DeltaTable()

    terms.foreach { case (f, t) =>
      // Initialize with trivial decompositions of size 1
      t.foreach(e => deltaTable.add(f, e::Nil, e::Nil, FOLVar(new VariableStringSymbol("alpha"))) )

      for (n <- 2 until t.length+1) {
        // Take only the decompositions of term sets of size (n-1) from the current delta table
        val one_less = deltaTable.getDecompositionsOfSize(n-1)

        one_less.foreach { case (s, forms) =>
          // If this formula's terms have a decomposition with this s
          if(forms.contains(f)) {
            val pairs = deltaTable.get(s, f)

            // Iterate over the list of decompositions
            pairs.foreach { case (u, ti) =>
              // Only choose terms that are after the last term in tl
              val maxIdx = t.lastIndexWhere(e => ti.contains(e))
              val termsToAdd = t.slice(maxIdx + 1, (t.size + 1))
         
              // Compute delta of the incremented list
              termsToAdd.foreach {case e =>
                val incrementedtermset = ti :+ e
                val p = delta(incrementedtermset)
           
                // If non-trivial
                if (p._2 != (incrementedtermset)) {
                  // Update delta-table
                  deltaTable.add(f, incrementedtermset, p._2, p._1)
                }
              }

            }
          }
        }
      }
    } 

    deltaTable
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

