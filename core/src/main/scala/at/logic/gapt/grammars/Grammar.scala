/*
 * Grammar that generates a list of terms T
 *
 * NOTE: This is not the implementation of a grammar in the usual sense.
 * Here we keep only two sets, U and S, for the grammar with start symbol 'τ',
 * non-terminal 'α' and production rules
 * P = { τ -> u | u in U} union { α -> s | s in S }
 */

package at.logic.gapt.grammars

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol._

/**
 * Takes a set of terms and, using DeltaG, computes the set of smallest grammars that generate it.
 */
object ComputeGrammars {

  def apply( terms: List[FOLTerm], delta: DeltaVector ): List[VectTratGrammar] = {
    // TODO: when iterating for the case of multiple cuts, change this variable.
    val eigenvariable = "α"
    val deltatable = new DeltaTable( terms, eigenvariable, delta )

    findValidGrammars( terms, deltatable, eigenvariable ).sortWith( ( g1, g2 ) => g1.size < g2.size )
  }

  /**
   * Finds valid, minimum-size grammars based on a list of terms and a generalized delta table.
   *
   *
   * @param terms The terms to be compressed.
   * @param deltatable A generalized delta table for terms.
   * @param eigenvariable The name of eigenvariables to introduce.
   */
  def findValidGrammars( terms: List[FOLTerm], deltatable: DeltaTable, eigenvariable: String, axiom: FOLVar = FOLVar( "τ" ) ): List[VectTratGrammar] = {

    //Helper functions for grammars

    //The number of terms this grammar compresses (grammars that "compress" only one term are useless and
    //hence discarded here.)
    def numTerms( s: Set[List[FOLTerm]], t: List[FOLTerm] ) = if ( s.size != 0 ) s.size else t.size

    // This gets decremented as iterating through the delta table reveals
    // smaller and smaller grammars. The initial value is the size of the trivial decomposition
    // (alpha,terms)
    var smallestGrammarSize = terms.size

    // Exact computation of the smallest coverings. Returns only these. Memory-aware implementation.
    // s is the key of the delta table and pairs is a list of (u,T), where s applied to u = T.
    def smallestCoverExact( s: Set[List[FOLTerm]], pairs: List[( FOLTerm, List[FOLTerm] )] ) = {

      // |U| + |S| < |T|
      // We only need to consider subsets of size |smallestGrammar| - |S| or less
      val maxSubsetSize = smallestGrammarSize - s.size

      //val subsets = all subsets pairs of size (1..maxSubsetSize)
      lazy val subsets = ( 1 to maxSubsetSize ).toList.foldLeft( Iterator[Set[( FOLTerm, List[FOLTerm] )]]() ) {
        case ( acc, i ) => pairs.toSet.subsets( i ) ++ acc
      }

      // Supposedly these subsets are in increasing order of size, 
      // so the lazy structure will not have to load the bigger ones.
      var coverSize = maxSubsetSize

      //Returns the smallest subset {(u1,T1),...,(un,Tn)} of a line in the delta table
      //such that. Union(T1,...,Tn) + C = terms, where C are some constant terms.
      def getSmallestSubsets( subsets: Iterator[Set[( FOLTerm, List[FOLTerm] )]] ): List[List[FOLTerm]] = {
        if ( subsets.hasNext ) {

          val set = subsets.next()

          if ( set.size <= coverSize ) {
            //Create the union of the pairs in the subset and check whether it amounts to <terms>
            val ( u, t ) = set.foldLeft( ( List[FOLTerm](), List[FOLTerm]() ) ) {
              case ( acc, ( u, t ) ) =>
                ( u :: acc._1, t ++ acc._2 )
            }

            val difference = terms.diff( t )

            //Union(T1,...,Tn) = terms => we are finished
            if ( difference.size == 0 ) {
              coverSize = set.size
              u :: getSmallestSubsets( subsets )
            } //Some constant terms need to be added => add the difference to coverSize
            else if ( u.size + difference.size <= coverSize ) {
              coverSize = u.size + difference.size
              ( u ++ difference ) :: getSmallestSubsets( subsets )
            } else {
              getSmallestSubsets( subsets )
            }

          } else {
            List()
          }
        } else List()
      }

      val coverings = getSmallestSubsets( subsets )
      smallestGrammarSize = s.size + coverSize

      coverings
    }

    //Go through the rows of the delta table and find the smallest
    //covering in each row.
    deltatable.table.foldLeft( List[VectTratGrammar]() ) {
      case ( grammars, ( s, pairs ) ) =>

        // Ignoring entries where s.size == 1 because they are trivial
        // grammars with the function symbol on the right.
        if ( numTerms( s, pairs.headOption.map( _._2 ).getOrElse( Nil ) ) > 1 ) {

          // Add the trivial decomposition {alpha_0} o s if s only has one vector
          val ev = FOLVar( eigenvariable + "_0" )
          val newpairs = if ( s.size == 1 && s.head.forall( e => terms.contains( e ) ) ) { ( ev, s.head ) :: pairs } else pairs

          val evs = newpairs.foldLeft( List[FOLVar]() )( {
            case ( acc, p ) =>
              val t = p._1
              acc ++ freeVariables( t ).toList
          } ).distinct

          // Whenever we find a smaller S-vector,
          // we add the grammars in its row to the list of returned ones.
          if ( s.size < smallestGrammarSize ) {

            val coverings = smallestCoverExact( s, newpairs )

            coverings.foldLeft( grammars ) {
              case ( acc, u ) =>
                VectTratGrammar( axiom, Seq( List( axiom ), evs ),
                  u.map( List( axiom ) -> List( _ ) ).toSet ++ s.map( evs -> _ ) ) :: acc
            }
          } else grammars

        } else {
          grammars
        }
    }
  }

}

