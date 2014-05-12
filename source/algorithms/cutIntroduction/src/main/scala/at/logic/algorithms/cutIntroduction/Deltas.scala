
package at.logic.algorithms.cutIntroduction

import at.logic.algorithms.interpolation._
import at.logic.algorithms.lk._
import at.logic.algorithms.lk.statistics._
import at.logic.algorithms.resolution._
import at.logic.calculi.expansionTrees.{ExpansionTree, ExpansionSequent, toSequent, quantRulesNumber => quantRulesNumberET}
import at.logic.calculi.lk._
import at.logic.calculi.lk.base._
import at.logic.calculi.occurrences._
import at.logic.language.fol.Utils._
import at.logic.language.fol._
import at.logic.language.hol.logicSymbols._
import at.logic.provers.Prover
import at.logic.provers.eqProver.EquationalProver
import at.logic.provers.minisat.MiniSATProver
import at.logic.provers.prover9.Prover9Prover
import at.logic.transformations.herbrandExtraction.extractExpansionTrees
import at.logic.utils.dssupport.ListSupport._
import at.logic.utils.executionModels.timeout._
import at.logic.utils.logging.Logger

import scala.collection.immutable.HashMap

/** Represents the vector Delta(t_1,...,t_n), i.e. one row of the Delta-table
  * (for details, see gapt/doc/deltavector.tex, Chapter "Generalized Delta-Vector").

  * A delta-vector computes the common structure and the differences between the terms of a termset.
  * This is realized by returning a set of tuples (u,S), where u is a term containing the parts
  * common to all supplied terms. It contains numbered eigenvariables where the terms diverged.
  * S is a list of lists (one list for each introduced eigenvariable), which contains the
  * lists of different terms which must be substituted for the eigenvariables to get the
  * original termset.
  *
  * Each member of the returned set is a valid decomposition, though, depending on the
  * kind of delta vector, this set may contain 0, 1, or many elements.
  */
trait DeltaVector {
  def computeDelta(terms: List[FOLTerm], eigenvariable: String) : Set[types.Decomposition]
}

/** Contains the implementations for the various delta-vectors.
  */
object Deltas extends Logger {


  /** The delta-vector which uses at most one variable in its decompositions.
    *
    * [OneVariableDelta] will return exactly one decomposition; if all terms are equal, it will return simply the first
    * term for u and Nil for s. If they are not equal, it will return some u and
    * an S consisting s-vectors of size 1.
    *
    * The variable in the returned decomposition -- if it occurrs -- will be named [eigenvariable]_0.
    */
  class OneVariableDelta extends DeltaVector with Logger {
    // There must be a better way...
    // TODO: this should go somewhere else?
    def listEquals(lst1: List[FOLTerm], lst2: List[FOLTerm]) : Boolean = (lst1, lst2) match {
      case (Nil, Nil) => true
      case (hd1::tl1, hd2::tl2) => (hd1.syntaxEquals(hd2)) && listEquals(tl1, tl2)
      case (_, _) => false
    }

    def computeDelta(terms: List[FOLTerm], eigenvariable: String) : Set[types.Decomposition] = {
      val (u,s1) = computeDg(terms, FOLVar(eigenvariable + "_0"))

      val s2 = s1.map(x => List(x))

      Set((u,Set(s2: _*)))
    }

    // Delta difference
    def computeDg(terms: List[FOLTerm], eigenvariable: FOLVar) : (FOLTerm, List[FOLTerm]) = terms.size match {
      // IMPORTANT!!!!
      // With this, the constant decomposition is not found. Without this, the constant decomposition is the only one found.
      case 1 => return (eigenvariable, terms)
      case _ => terms.head match {
        // If the variables are reached
        case FOLVar(_) | FOLConst(_) =>
          // If all variables are equal
          if ( terms.forall(t => t.syntaxEquals(terms.head)) ) { return (terms.head, Nil) }
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
            val deltaOfArgs = listOfArgs.foldRight(List[(FOLTerm, List[FOLTerm])]()) ((a, acc) => computeDg(a, eigenvariable) :: acc)
           
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

  /** The delta-vector which only returns decompositions with exactly
    * [numVars] variables.
    *
    * Since decompositions with exactly [numVars] variables might not
    * exist, [computeDelta] might return 0 decompositions, and since many
    * might exist, it might return more than one for a given set of terms.
    *
    * The variables in the returned decompositions will be named 
    * [eigenvariable]_0,...
    *
    * For details, see doc/deltavector.tex, Section "bounded generalized Delta-Vector".
    */
  class ManyVariableDelta(numVars: Int) extends DeltaVector with Logger {
    val upperBound = numVars

    def computeDelta(terms: List[FOLTerm], eigenvariable: String) : Set[types.Decomposition] = {
      computeDg(terms, eigenvariable, 0).map{
        case(u,s,_) => {
          val s2 = Set(s.transpose: _*)
          (u,s2)
        }}
    }

    private def computeDg(terms: List[FOLTerm], eigenvariable: String, curInd: Int) : Set[(types.U,types.RawS,Int)] = {

      //Special case: only one term has been provided. This isn't part of
      //the definition of DeltaG in the paper (deltavector.tex), but
      //decompositions of the form (a,t.head) must be added to give the delta table a starting point.
      if (terms.size == 1) {
        Set((FOLVar(eigenvariable + "_" + curInd), List(terms), curInd+1))
      }
      //The case distinction of Delta_G.
      //   First case: all terms are equal -> take one and put it into u (with no variables and curInd unchanged).
      //   Second case: all terms begin with the same function symbol AND
      //                (that function is unary OR (RANDOM=true we won't need more than [numVars] variables) -> recurse.
      //   Third case: otherwise -> create a new variable with the terms as s-vector and increment curInd.
      //   The second & third case are chosen partly non-deterministically:
      //   recursing with a unary function symbol is "free" (in the sense of not increasing the number of needed variables)
      //   but otherwise, we have to choose both the 2nd and 3rd cases.
      else if (terms.tail.forall(t => (t.syntaxEquals(terms.head)))) {
        Set((terms.head, Nil, curInd))
      }
      else
      {
        //Compute Delta_G(u_i) for all u_i
        //computePart is the only part which is significanlty different from
        //its counterpart in UnboundedVariableDelta, since it has to compute all combinations of choices
        //between the second & third cases.
        def computePart(acc:Set[(List[types.U], types.RawS, Int)], ts: List[FOLTerm]) : Set[(List[types.U], types.RawS, Int)] = {
          acc.flatMap{
            case(u,s,ind) => computeDg(ts, eigenvariable, ind).map{
              case (uPart, sPart, newInd) => (u :+ uPart, s ++ sPart, newInd) } }
        }

        var results = Set[(types.U, types.RawS, Int)]()

        //We choose the second case and filter out all the results with too many variables, then apply nub.
        if (commonFuncHead(terms)) {
          val recursionResults = terms.map(t => fromFuncArgs(t)).transpose.foldLeft(Set((Nil:List[types.U], Nil:types.RawS, curInd)))(computePart)
          val filteredResults = recursionResults.filter{ case(_,s,_) => s.distinct.length <= upperBound}

          //Apply nub to each result
          val nubbedResults = filteredResults.map{ case (uParts, rawS, ind) =>
            val rawU = Function(fromFunc(terms.head), uParts)

            val (u,s) = nub(smallestVarInU(eigenvariable, rawU), eigenvariable, rawU, rawS)

            (u,s, ind)
          }

          results = results ++ nubbedResults
        }

        //We also choose the third case, provided that the terms don't begin with a common, unary function symbol
        if (!commonFuncHead(terms) || fromFuncArgs(terms.head).length != 1) {
          results = results + ((FOLVar(eigenvariable + "_" + curInd), List(terms), curInd+1))
        }

        results
      }
    }
  }

  /** The delta-vector which has no upper limit on the number of variables
    * it may use in its decompositions.
    *
    * Here [computeDelta] will return exactly one decompositions with an
    * a priori unknown number of variables. Different terms will result in
    * different numbers of variables being introduced.
    *
    * The variables in the returned decompositions will be named 
    * [eigenvariable]_0,...
    */
  class UnboundedVariableDelta extends DeltaVector with Logger {
    /** Computes Delta_G(t_1,...,t_n) for a list of terms t_1,...,t_n
      * and returns (u;s_1,...s_q) where u is a term containing the variables α_1,...,α_q
      * and the lists s_1,...,s_q are the values which must be substituted for these α to
      * get back the original t_1,...,t_n.
      *
      * For details, see gapt/doc/deltavector.tex, Chapter "Generalized Delta-Vector".
      * 
      * @param terms The terms t_1,...,t_n.
      * @param eigenvariable The name of the variables to insert into u. The default is "α".
      * @return The tuple (u:FOLTerm, s:types.RawS).
        Replacing α_1,...,α_q with s[1][i],...,s[q][i] results in t_i.
      */
    def computeDelta(terms: List[FOLTerm], eigenvariable: String) : Set[types.Decomposition] = {
      //Set(computeDg(terms, eigenvariable, 0)._1)

      val (rawU,rawS) = computeDg(terms, eigenvariable, 0)._1

      val (nubbedU,nubbedS) = nub(smallestVarInU(eigenvariable, rawU), eigenvariable, rawU, rawS)

      val transposedS = Set(nubbedS.transpose: _*)

      Set((nubbedU, transposedS))
    }

    /** Computes Delta_G. Called by delta.apply.
      *
      * @param terms The terms t_1,...,t_n.
      * @param eigenvariable The name of the variables to insert into u.
      * @param curInd A counter; the index which is to be assigned to the first newly introduced α. Default is 0.
      * @return ((u,S),newInd) - the first tuple contains the term u and the list S, the second component is the
      * number of introduced α.
      */
    private def computeDg(terms: List[FOLTerm], eigenvariable: String, curInd: Int) : (types.RawDecomposition,Int) = {

      trace("----------- entering computeDg.")
      trace("   terms: " + terms)
      trace("   curInd: " + curInd)

      //Special case: only one term has been provided. This isn't part of
      //the definition of DeltaG in the paper (deltavector.tex), but
      //decompositions of the form (a,t.head) must be added to give the delta table a starting point.
      if (terms.size == 1) {
        ((FOLVar(eigenvariable + "_" + curInd), List(terms)), curInd+1)
      }
      //The case distinction of Delta_G.
      //   First case: all terms are equal -> take one and put it into u (with no variables and curInd unchanged).
      //   Second case: all terms begin with the same function symbol -> recurse.
      //   Third case: otherwise -> create a new variable with the terms as s-vector and increment curInd.
      else if (terms.tail.forall(t => (t.syntaxEquals(terms.head)))) {
        ((terms.head, Nil), curInd)
      }
      else if (commonFuncHead(terms)) {
          //Compute Delta_G(u_i) for all u_i
          def computePart(acc:(List[types.U], types.RawS,Int), ts: List[FOLTerm]) : (List[types.U], types.RawS, Int) = {
            val ((uPart,sPart),i:Int) = computeDg(ts, eigenvariable, acc._3)
            (acc._1 :+ uPart, acc._2 ++ sPart, i)
          }
          
          //Get the function args (unapply._2) and fold with computePart
          //The result might contain duplicate variables and therefore, nub must be applied
          val (rawUParts, s, newInd) = terms.map(t => fromFuncArgs(t)).transpose.foldLeft((Nil:List[types.U], Nil:types.RawS, curInd))(computePart)

          //trace("computePart finished. Results(u,S):")
          //trace(rawUParts.toString())
          //trace(rawS.toString())

          //Reapply the function head to the pieces
          val u = Function(fromFunc(terms.head), rawUParts)

          //trace("rawU: " + rawU)
          //trace("smallest Var in rawU: " + smallestVarInU(eigenvariable, rawU))

          //val (u,s) = nub(smallestVarInU(eigenvariable, rawU), eigenvariable, rawU, rawS)

          //computePart naively increased newInd, but nub reduces the number of variables again
          //val nubbedInd = largestVarInU(eigenvariable, u)

          trace("final (u | S): " + u + " | " + s)
          //trace("newInd(" + (if (nubbedInd.nonEmpty) "exists" else "does not exist") + "): " + (if (nubbedInd.nonEmpty) nubbedInd.get + 1 else curInd))

          //((u,s), if (nubbedInd.nonEmpty) nubbedInd.get + 1 else curInd)
          ((u,s), newInd)
      } else {
          ((FOLVar(eigenvariable + "_" + curInd), List(terms)), curInd+1)
      }
    }
  }


  //------------------------Helper functions---------------------------------/

  /** returns true iff all given terms begin with the same function symbol & the same arity.*/
  private def commonFuncHead(terms:List[FOLTerm]) = {
    if (isFunc(terms.head)) {
      terms.tail.forall(isFunc(_:FOLTerm, (fname => fname == fromFunc(terms.head).toString))) &&
      terms.map(fromFuncArgs(_).length).distinct.length <= 1
    } else false
  }

  /** Returns the smallest variable index occurring in a term u.
    * Variable names are expected to be of the form [eigenvariable]_[i],
    * where i is the variable index. If u has no variables, None is returned.
    *
    * This function is used for nub.
    */
  private def smallestVarInU(eigenvariable: String, u: types.U) : Option[Int] = {
    def extractIndex(x:FOLVar) = x.toString.substring(eigenvariable.length + 1, x.toString.length).toInt

    val res = collectVariables(u).filter(isEigenvariable(_:FOLVar,eigenvariable)).map(extractIndex)
    if (res.length == 0) None else Some(res.min)
  }

  /** Returns the largest variable index occurring in a term u.
    * Variable names are expected to be of the form [eigenvariable]_[i],
    * where i is the variable index. If u has no variables, None is returned.
    */
  private def largestVarInU(eigenvariable: String, u: types.U) : Option[Int] = {
    def extractIndex(x:FOLVar) = x.toString.substring(eigenvariable.length + 1, x.toString.length).toInt

    val res = collectVariables(u).filter(isEigenvariable(_:FOLVar,eigenvariable)).map(extractIndex)
    if (res.length == 0) None else Some(res.max)
  }

  /** Duplicate-eliminating function; merges those α in u which have identical term-lists in s.
    * If a contiguous set α_k,...,α_(k+q) of variables was present in u before the merging, a contiguous
    * set α_k,...,α_(k+p) (0<=p<=q) of variables will be present in the return value u'.
    * 
    * @param beginWith The smallest index of any alpha occurring in u. If this is None, nothing is done.
    * @param eigenvariable The name of the eigenvariables in u. Default is "α".
    * @param u The term u of the substitution which contains α-instances.
    * @param s The list of terms belonging to the α-instances.
    * @param (u',s') s.t. all α with identical corresponding term-lists in s have been merged together in u
    * and all duplicate lists s have been reduced to only 1 occurrence.
    */
  private def nub (beginWith: Option[Int], eigenvariable:String, u: types.U, s: types.RawS): types.RawDecomposition = beginWith match {
    case None => (u,s)
    case Some(start) => {
      val indexedS = s.zip(start to (start + s.size - 1))

      trace("    nub | indexedS = " + indexedS)

      //Get the list of all variables occurring in u
      var presentVars = collectVariables(u).filter(isEigenvariable(_:FOLVar, eigenvariable)).distinct

      trace("    nub | presentVars = " + presentVars)

      //Go through s, look ahead for duplicates, and delete them.
      def nub2(u: types.U, s: List[(List[FOLTerm],Int)]) : types.RawDecomposition = s match {
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
            trace("        | deleting duplicate " + eigenvariable + "_" + dupl._2 )
            presentVars = presentVars.filter(pv => pv.toString != (eigenvariable + "_" + dupl._2))
            trace("        | now present vars: " + presentVars)
            replaceFreeOccurenceOf(eigenvariable + "_" + dupl._2, eigenvariable + "_" + ind, curU)
          })

          val ret = nub2(newU, rest)
          (ret._1, lst::ret._2)
        }
      }

      //Merge duplicate vars in u and delete elements of s.
      val (swissCheeseU,newS) = nub2(u, indexedS)

      trace("    nub | (swCU, newS) = " + (swissCheeseU,newS))

      //Merging with nub2 will have created holes in u => reindex the variables in u to get a contiuous segment
      val renamings = presentVars.toList.sortBy(x => x.toString).zip(start to (presentVars.size - 1))

      trace("    nub | renamings (there are " + renamings.length + ") = " + renamings)

      val reindexedU = renamings.foldLeft(swissCheeseU) {(curU,ren) => 
        trace("        | rename: " + ren._1 + " -> " + eigenvariable + "_" + ren._2)
        val ret = replaceFreeOccurenceOf(ren._1.toString, eigenvariable + "_" + ren._2, curU)
        trace("        | result: " + ret)
        ret
      }

      (reindexedU, newS)
    }
  }
}
