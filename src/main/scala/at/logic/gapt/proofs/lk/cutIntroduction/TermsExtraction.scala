/**
 * Extraction of terms for the cut-introduction algorithm.
 *
 * NOTE: Prenex formulas only.
 *
 * Collects all tuples of terms used to instantiate blocks of quantifiers and
 * stores these tuples in a map. The map associates each formula with the
 * respective tuples used to instantiate its quantifier block.
 * In order to use the term set in the cut-introduction algorithm, the map is
 * transformed into a single list of terms (termset) where the tuples of each
 * formula are prefixed with a fresh function symbol "f_i". This transformation
 * is done by the TermSet class, which stores the new term set and the mapping
 * of fresh function symbols to their respective formulas.
 *
 * Example:
 *
 * Map:
 * F1 -> [(a,b), (c,d)]
 * F2 -> [(e), (f), (g)]
 *
 * List of terms (termset):
 * [f_1(a,b), f_1(c,d), f_2(e), f_2(f), f_2(g)]
 *
 * Name mapping (formulaFunction):
 * f_1 -> F1
 * f_2 -> F2
 *
 */

package at.logic.gapt.proofs.lk.cutIntroduction

import at.logic.gapt.expr._
import at.logic.gapt.proofs.expansionTrees._
import at.logic.gapt.proofs.lk._
import at.logic.gapt.proofs.lk.base._

@deprecated( "Use InstanceTermEncoding instead." )
object TermsExtraction {
  def apply( proof: LKProof ): TermSet = apply( LKToExpansionProof( proof ) )

  def apply( expProof: ExpansionSequent ): TermSet = {
    val encoding = InstanceTermEncoding( toShallow( expProof ) )

    new TermSet( encoding, groundTerms( encoding.encode( expProof ) ).toList )
  }
}

// Given a map with keys (F => { t_1, ..., t_n } ), where the t_i are lists of terms,
// this represents a set of terms containing, for every such key, the terms g_F( t_1 ), ..., g_F( t_n ),
// where g_F is a function symbol associated with the formula F. Functions to go back and forth
// between the input map and the representation are provided.
@deprecated( "Use InstanceTermEncoding instead." )
class TermSet( encoding: InstanceTermEncoding, val set: List[FOLTerm] ) {

  def formulas = set.map { case FOLFunction( f, _ ) => encoding.findESFormula( f ).get._1 }

  // Given g_F( t_i ) as above, return F.
  def getFormula( t: FOLTerm ): FOLFormula = t match {
    case FOLFunction( f, _ ) => encoding.findESFormula( f ).get._1
  }

  // Given g_F( t_i ) as above, return t_i.
  def getTermTuple( t: FOLTerm ): List[FOLTerm] = t match {
    case FOLFunction( _, tuple ) => tuple
  }
}
