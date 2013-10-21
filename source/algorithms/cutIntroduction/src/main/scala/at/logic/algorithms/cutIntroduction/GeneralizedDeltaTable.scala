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
import at.logic.language.lambda.symbols.VariableStringSymbol
import at.logic.calculi.occurrences._
import scala.collection.immutable.HashMap
import at.logic.utils.dssupport.ListSupport._
import at.logic.utils.logging.Logger

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
class GeneralizedDeltaTable(terms: List[FOLTerm], eigenvariable: String) extends Logger {

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
    val one_less = table.filter( e => safeHead(e._1,Nil).length == n - 1) // (e._1.isEmpty && n==1) || (n !=1 && e._1.head.length == n-1)

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
          val p = deltaG(incrementedtermset, eigenvariable)

          trace("---------------------------------------------------------")
          trace("Computed deltaG of " + incrementedtermset)
          trace("Result:")
          trace("u: " + p._1)
          trace("s: " + p._2)
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
          if (incrementedtermset.size == 1 || p._1 != trivialEv) { //p._2.size == 1 || p._1 != FOLVar(eigenvariable + "") safeHead(p._2, Nil) != (incrementedtermset)) {
            // Update delta-table
            add(p._2, p._1, incrementedtermset)
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

/** Represents Delta_G(t_1,...,t_n), i.e. one row of the Delta-table
  * (for details, see gapt/doc/deltavector.tex, Chapter "Generalized Delta-Vector").

  * Delta.apply computes the common structure and the differences between the terms of a termset.
  * This is realized by returning a tuple (u,S), where u is a term containing the parts
  * common to all supplied terms. It contains numbered eigenvariables where the terms diverged.
  * S is a list of lists (one list for each introduced eigenvariable), which contains the
  * lists of different terms which must be substituted for the eigenvariables to get the
  * original termset.
  */
object deltaG extends Logger {
  /** Computes Delta_G(t_1,...,t_n) for a list of terms t_1,...,t_n
    * and returns (u;s_1,...s_q) where u is a term containing the variables α_1,...,α_q
    * and the lists s_1,...,s_q are the values which must be substituted for these α to
    * get back the original t_1,...,t_n.
    *
    * For details, see gapt/doc/deltavector.tex, Chapter "Generalized Delta-Vector".
    * 
    * @param terms The terms t_1,...,t_n.
    * @param eigenvariable The name of the variables to insert into u. The default is "α".
    * @return The tuple (u:FOLTerm, s:List[List[FOLTerm]]).
      Replacing α_1,...,α_q with s[1][i],...,s[q][i] results in t_i.
    */
  def apply(terms: List[FOLTerm], eigenvariable: String) : types.Decomposition = computeDg(terms, eigenvariable, 0)._1

  /** Computes Delta_G. Called by delta.apply.
    *
    * @param terms The terms t_1,...,t_n.
    * @param eigenvariable The name of the variables to insert into u.
    * @param curInd A counter; the index which is to be assigned to the first newly introduced α. Default is 0.
    * @return ((u,S),newInd) - the first tuple contains the term u and the list S, the second component is the
    * number of introduced α.
    */
  private def computeDg(terms: List[FOLTerm], eigenvariable: String, curInd: Int) : (types.Decomposition,Int) = {
    /** Returns whether t is a function. */
    def isFunc1(t:FOLTerm) = isFunc(t,_ => true)

    /** Returns whether t is a variable. */
    def isVar(t:FOLTerm) = t match {
      case FOLVar(_) => true
      case _ => false
    }

    /** Returns whether t is a function whose name fulfills to a given condition. */
    def isFunc(t:FOLTerm, cond: String => Boolean) = t match {
      case Function(f,_) => cond(f.toString)
      case _ => false
    }

    /** Unsafely extracts the function name from a term. Fails if the term is not a function. */
    def fromFunc(t:FOLTerm) = t match { case Function(f,_) => f }
    def fromFuncArgs(t:FOLTerm) = t match { case Function(_,a) => a}

    //True iff all terms begin with the same function symbol.
    def commonFuncHead(terms:List[FOLTerm]) = terms.tail.forall(isFunc(_:FOLTerm, (fname => fname == fromFunc(terms.head).toString)))


    //Special case: only one term has been provided. This isn't part of
    //the definition of DeltaG in the paper (deltavector.tex), but
    //decompositions of the form (a,t.head) must be added to give the delta table a starting point.
    if (terms.size == 1) {
      ((FOLVar(new VariableStringSymbol(eigenvariable + "_" + curInd)), List(terms)), curInd+1)
    }
    //The case distinction of Delta_G.
    //   First case: all terms are equal -> take one and put it into u (with no variables and curInd unchanged).
    //   Second case: all terms begin with the same function symbol -> recurse.
    //   Third case: otherwise -> create a new variable with the terms as s-vector and increment curInd.
    else if (terms.tail.forall(t => (t =^ terms.head))) {
      ((terms.head, Nil), curInd)
    }
    else if (commonFuncHead(terms)) {
        var newInd = curInd

        //Compute Delta_G(u_i) for all u_i
        def computePart(acc:(List[types.U], types.S), ts: List[FOLTerm]) : (List[types.U], types.S) = {
          val ((uPart,sPart),i:Int) = computeDg(ts, eigenvariable, newInd)
          newInd = i
          (acc._1 :+ uPart, acc._2 ++ sPart)
        }
        
        //Get the function args (unapply._2) and fold with computePart
        //The result might contain duplicate variables and therefore, nub must be applied
        val (rawUParts, rawS) = terms.map(fromFuncArgs).transpose.foldLeft((Nil:List[types.U], Nil:types.S))(computePart)

        trace("computePart finished. Results(u,S):")
        trace(rawUParts.toString())
        trace(rawS.toString())

        //Reapply the function head to the pieces
        val rawU = Function(fromFunc(terms.head), rawUParts)

        trace("rawU: " + rawU)
        trace("smallest Var in rawU: " + smallestVarInU(eigenvariable, rawU))

        val (u,s) = nub(smallestVarInU(eigenvariable, rawU), eigenvariable, rawU, rawS)

        trace("final (u | S): " + u + " | " + s)
        trace("newInd: " + newInd)

        ((u,s), newInd)
    } else {
        ((FOLVar(new VariableStringSymbol(eigenvariable + "_" + curInd)), List(terms)), curInd+1)
    }
  }

  //------------------------Helper functions---------------------------------/

  /** Returns the smallest variable index occurring in a term u.
    * Variable names are expected to be of the form [eigenvariable]_[i],
    * where i is the variable index.
    */
  private def smallestVarInU(eigenvariable: String, u: types.U) : Int = u match {
    case Function(_,terms) => if (terms.length == 0) { 0 } else { terms.map(t => smallestVarInU(eigenvariable, t)).min }
    case FOLVar(x) => x.toString.substring(eigenvariable.length + 1, x.toString.length).toInt
  }

  /** Duplicate-eliminating function; merges those α in u which have identical term-lists in s.
    * If a contiguous set α_k,...,α_(k+q) was present in u before the merging, a contiguous
    * set α_k,...,α(k+p) (0<=p<=q) will be present in the return value u'.
    * 
    * @param beginWith The smallest index of any alpha occurring in u.
    * @param eigenvariable The name of the eigenvariables in u. Default is "α".
    * @param u The term u of the substitution which contains α-instances.
    * @param s The list of terms belonging to the α-instances.
    * @param (u',s') s.t. all α with identical corresponding term-lists in s have been merged together in u
    * and all duplicate lists s have been reduced to only 1 occurrence.
    */
  private def nub (beginWith: Int, eigenvariable:String, u: types.U, s: types.S): types.Decomposition = {
    val indexedS = s.zip(beginWith to (beginWith + s.size - 1))

    trace("    nub | indexedS = " + indexedS)

    //Get the list of all variables occurring in u
    var presentVars = collectVars(u).distinct

    trace("    nub | presentVars = " + presentVars)

    //Go through s, look ahead for duplicates, and delete them.
    def nub2(ev: String, u: types.U, s: List[(List[FOLTerm],Int)]) : types.Decomposition = s match {
      //no variables in u -> just return (u,Nil)
      case Nil => (u,s.unzip._1)
      //variables occur -> check xs for identical s-vectors
      case ((lst,ind)::xs) => {
        //The duplicates are all the duplicates of lst. The rest is lst + all vectors not identical to it.
        val (duplicates,rest) = xs.partition(y => y._1 == lst)

        trace("    nub2 | duplicates,rest = " + (duplicates,rest))

        //go through all duplicates, rename the corresponding variables in u to ev_[ind]
        //and delete ev_[x] from presentvars
        val newU = duplicates.foldLeft(u)((curU, dupl) => {
          presentVars = presentVars.filter(pv => pv != ev + "_" + dupl._2)
          renameVar(curU, ev + "_" + dupl._2, ev + "_" + ind)
        })

        val ret = nub2(eigenvariable, newU, rest)
        (ret._1, lst::ret._2)
      }
    }

    //Merge duplicate vars in u and delete elements of s.
    val (swissCheeseU,newS) = nub2(eigenvariable, u, indexedS)

    trace("    nub | (swCU, newS) = " + (swissCheeseU,newS))

    //Merging with nub2 will have created holes in u => reindex the variables in u to get a contiuous segment
    val renamings = presentVars.toList.sorted.zip(beginWith to (presentVars.size - 1))
    val reindexedU = renamings.foldLeft(swissCheeseU) ((curU,ren) => renameVar(curU, eigenvariable + "_" + ren._1, eigenvariable + "_" + ren._2))

    (reindexedU, newS)
  }

  /** Returns the set of variables occurring in a FOL term which consists only of functions and variables. */
  private def collectVars(u: types.U) : List[String] = u match {
    case Function(_,terms) => terms.map(collectVars).foldLeft(Nil:List[String])(_ ++ _)
    case FOLVar(x) => List(x.toString)
  }

  /** Renames a variables in u from oldName to newName */
  private def renameVar(u : types.U, oldName: String, newName: String) : types.U = u match {
    case Function(f,terms) => Function(f, terms.map(x => renameVar(x,oldName,newName)))
    case FOLVar(x) => if (x.toString() == oldName) { FOLVar(new VariableStringSymbol(newName)) } else { FOLVar(x) }
  }
}
