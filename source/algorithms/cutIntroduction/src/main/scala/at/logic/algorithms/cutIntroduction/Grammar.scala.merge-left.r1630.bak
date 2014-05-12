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
import at.logic.language.hol.logicSymbols._
import at.logic.utils.dssupport.ListSupport._
import at.logic.utils.dssupport.MapSupport._
import at.logic.utils.logging.Logger
import at.logic.utils.executionModels.searchAlgorithms.SetNode
import at.logic.utils.executionModels.searchAlgorithms.SearchAlgorithms.{DFS, BFS, setSearch}


class Grammar(u0: List[FOLTerm], s0: List[FOLTerm], ev: FOLVar) {

  val u = u0
  val s = s0
  val eigenvariable = ev

  // Is this the best solution?
  var flatterms: FlatTermSet = null

  def size = u.size + s.size

/*
  def strictSuperGrammarOf(g : Grammar) = 
    // U o S \supset U' o S'
    // U \supset U' and S \supset S'
    g.u.forall(e => u.contains(e)) && g.s.forall(e => s.contains(e)) &&
    // |U| > |U'| or |S| > |S'|
    (u.size > g.u.size || s.size > g.s.size)
*/

  def toPrettyString : String = "{ " + u.foldRight("")((ui, str) => str + ui + ", ") + " } o { " + s.foldRight("") ((si, str) => str + si + ", " ) + " }" 
  override def toString() : String = {
    "{ " + u.foldRight("")((ui, str) => str + ui + ", ") + " } o { " + s.foldRight("") ((si, str) => str + si + ", " ) + " }"
  }
}

object ComputeGrammars extends Logger {

  // This looks ugly :(
  def apply(terms: FlatTermSet) : List[Grammar] = apply(terms.termset).map{ case g => g.flatterms = terms; g }

  def apply(terms: List[FOLTerm]) : List[Grammar] = {
    // TODO: when iterating for the case of multiple cuts, change this variable.
    val eigenvariable = FOLVar(new VariableStringSymbol("α"))
    
    //debug( "computing delta-table" )
    val deltatable = new DeltaTable(terms, eigenvariable)
    //debug( "done computing delta-table" )
    //deltatable.printStats( { s => trace( "  " + s ) } )

    //debug( "reading off grammars from delta-table" )
    findValidGrammars(terms, deltatable, eigenvariable).sortWith((g1, g2) => g1.size < g2.size )
  }

  // Carbon copies of the apply methods that use findValidGrammars2.
  // These exist so that the old and the new solution may be tested side by side.
  // cutIntro in CutIntroduction.scala uses apply, cutIntro2, in addition to a more efficient version of improveSolution, uses apply2
 
  // Uses findValidGrammar2.
  def apply2(terms: FlatTermSet) : List[Grammar] = apply2(terms.termset).map{ case g => g.flatterms = terms; g }

  def apply2(terms: List[FOLTerm]) : List[Grammar] = {
    // TODO: when iterating for the case of multiple cuts, change this variable.
    val eigenvariable = FOLVar(new VariableStringSymbol("α"))
    
    //debug( "3rd version - computing delta-table" )
    val deltatable = new DeltaTable(terms, eigenvariable)
    //debug( "done computing delta-table" )
    //deltatable.printStats( { s => trace( "  " + s ) } )

    //debug( "reading off grammars from delta-table" )
    findValidGrammars2(terms, deltatable, eigenvariable).sortWith((g1, g2) => g1.size < g2.size )
  }

  def findValidGrammars(terms: List[FOLTerm], deltatable: DeltaTable, ev: FOLVar) : List[Grammar] = {

    deltatable.table.foldRight(List[Grammar]()) {case ((s, pairs), grammars) =>
      // Ignoring entries where s.size == 1 because they are trivial
      // grammars with the function symbol on the right.
      if(s.size != 1) {

        // Add the trivial decomposition {alpha} o s
        val newpairs = if(s.forall(e => terms.contains(e)) ) {
          (ev, s) :: pairs
        } else pairs
                                                              
        // Collect all possible subsets
        val allsubsets = subsets(newpairs)

        //trace( "folding allsubsets of newpairs" )
        //trace( "  pairs has size " + pairs.size )
        //trace( "  newpairs has size " + newpairs.size )
        //trace( "  allsubsets has size " + allsubsets.size )

        // For each subset, get the set U formed by the u_i's and the set T of the
        // terms covered (union of t_i)
        val subsetpairs = allsubsets.foldLeft(List[(List[FOLTerm], List[FOLTerm])]()) {(acc1, subset) =>
          val d = subset.foldLeft(List[FOLTerm](), List[FOLTerm]()) ( (acc2, el) => el._1 match {
            case null => acc2
            case _ => (el._1 :: acc2._1, tailRecUnion(el._2,acc2._2))
          })
          d :: acc1
        }
        //trace( "survived folding allsubsets of newpairs" )
       
        // Generate valid grammars
        // Note: each pair is ({u_1, ..., u_k}, {t_1, ..., t_j}) and for this to
        // be a valid decomposition, {t_1, ..., t_j} must contain all terms or
        // adding the missing terms to U should not exceed the size of the term
        // set.
        val ssize = s.size
        subsetpairs.foldLeft(grammars) {
          case (acc, p) =>
            val termsCovered = p._2
            val difference = terms.diff(termsCovered)
       
            // The grammar generates all the terms
            if(difference.size == 0) {
              (new Grammar(p._1, s, ev)) :: acc
            }
            // Some constants are added to U and this is still reasonably small
            else if(p._1.size + difference.size + ssize < terms.size) {
              //NOTE: p._1 ++ difference could cause a stack overflow, should difference grow too large.
              //Presently, this is not a problem.
              (new Grammar(p._1 ++ difference, s, ev)) :: acc
            }
            // No good
            else acc
        }
      }
      else grammars
    }
  }



  // Improve implementation of findValidGrammars.
  // In this method, the size of the smallest grammar found so far is kept, and
  // no grammar bigger than this is generated.
  def findValidGrammars2(terms: List[FOLTerm], deltatable: DeltaTable, ev: FOLVar) : List[Grammar] = {
    
    var smallestGrammarSize = terms.size

    // Exact computation of the smallest coverings. Returns only these.
    // Memory-aware implementation.
    def smallestCoverExact(s: List[FOLTerm], pairs: List[(FOLTerm, List[FOLTerm])], terms: List[FOLTerm]) = {

      // |U| + |S| < |T|
      // We only need to consider subsets of size |smallestGrammar| - |S| or less
      val maxSubsetSize = smallestGrammarSize - s.size

      // Trying a lazy list so that not all subsets are computed at once. 
      // BUT not sure if I am getting the behavior I expect...
      lazy val subsets = (1 to maxSubsetSize).toList.foldLeft(Iterator[Set[(FOLTerm, List[FOLTerm])]]()) {
        case (acc, i) => pairs.toSet.subsets(i) ++ acc
      }

      // Supposedly these subsets are in increasing order of size, 
      // so the lazy structure will not have to load the bigger ones.
      var coverSize = maxSubsetSize

      def getSmallestSubsets(subsets: Iterator[Set[(FOLTerm, List[FOLTerm])]]) : List[List[FOLTerm]] = {
        if(subsets.hasNext) {
          val set = subsets.next()
          if(set.size <= coverSize) {
            val (u, t) = set.foldLeft( ( List[FOLTerm](), List[FOLTerm]() ) ) { case (acc, (u, t)) => 
              ( u :: acc._1, tailRecUnion(t, acc._2) )
            }
            val difference = terms.diff(t)

            if(difference.size == 0) {
              coverSize = set.size
              u :: getSmallestSubsets(subsets) 
            } 
            else if(u.size + difference.size <= coverSize) {
              coverSize = u.size + difference.size
              (u ++ difference) :: getSmallestSubsets(subsets) 
            } 
            else getSmallestSubsets(subsets)
         
          } else List()
        } else List()
      }

      val coverings = getSmallestSubsets(subsets)
      smallestGrammarSize = s.size + coverSize
      coverings
    }

    deltatable.table.foldRight(List[Grammar]()) {case ((s, pairs), grammars) =>
      // Ignoring entries where s.size == 1 because they are trivial
      // grammars with the function symbol on the right.
      if(s.size != 1) {

        // Add the trivial decomposition {alpha} o s
        val newpairs = if(s.forall(e => terms.contains(e)) ) {
          (ev, s) :: pairs
        } else pairs

        if(s.size < smallestGrammarSize) {                    
          val coverings = smallestCoverExact(s, newpairs, terms)
          coverings.foldLeft(grammars) { case (acc, u) =>
            (new Grammar(u, s, ev) ) :: acc                   
          }                                                   
        } else grammars                                       
                                                                                                                            
      }
      else grammars
    }
  }




}
