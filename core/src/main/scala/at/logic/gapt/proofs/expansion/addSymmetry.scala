
package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol._

/**
 * Given an expansion sequent S which is a quasi-tautology (modulo symmetry),
 * returns an expansion sequent S' which is S extended by the symmetry instances
 * needed to make it a tautology.
 */
object addSymmetry {

  def apply( s: ExpansionSequent ): ExpansionSequent = {

    val deep_sequent = toDeep( s )
    val eq_ant = deep_sequent.antecedent.flatMap( f => getEqualityPairs( f, false ) )
    val eq_suc = deep_sequent.succedent.flatMap( f => getEqualityPairs( f, true ) )
    val polarized_eq = eq_ant ++ eq_suc
    val positive_pairs = polarized_eq.filter( t => t._3 ).map( t => ( t._1, t._2 ) )
    val negative_pairs = polarized_eq.filter( t => !t._3 ).map( t => ( t._1, t._2 ) )

    // Add p._2 = p._1 -> p._1 = p._2, thus changing the pair order
    val symm1 = positive_pairs.filter( p => negative_pairs.contains( ( p._2, p._1 ) ) ).map( p => ( p._2, p._1 ) )
    // Add p._1 = p._2 -> p._2 = p._1
    val symm2 = negative_pairs.filter( p => positive_pairs.contains( ( p._2, p._1 ) ) )

    val symm_terms = ( symm1 ++ symm2 ).distinct

    val x = FOLVar( "x" )
    val y = FOLVar( "y" )
    val eq = "="
    val eq1 = FOLAtom( eq, List( x, y ) )
    val eq2 = FOLAtom( eq, List( y, x ) )
    val imp = Imp( eq1, eq2 )
    val eq_symm = All( x, All( y, imp ) )

    val subs = symm_terms.map( p => Substitution( x -> p._1, y -> p._2 ) )

    if ( subs.length == 0 ) s
    else {

      val et = formulaToExpansionTree( eq_symm, subs.toList, false )

      // This expansion sequent should be a tautology.
      // (Not adding the expensive check)
      new ExpansionSequent( et +: s.antecedent, s.succedent )
    }
  }

  /**
   * Given a quantifier free formula f and polarity pol, returns all pairs of
   * terms which occur in the same equality predicate and its polarity.
   * pol is true for positive polarity.
   */
  def getEqualityPairs( f: HOLFormula, pol: Boolean ): List[( LambdaExpression, LambdaExpression, Boolean )] = f match {
    case Eq( t1, t2 )     => List( ( t1, t2, pol ) )
    case HOLAtom( p, _ )  => List()
    case Bottom() | Top() => List()
    case Neg( f1 )        => getEqualityPairs( f1, !pol )
    case And( f1, f2 )    => getEqualityPairs( f1, pol ) ++ getEqualityPairs( f2, pol )
    case Or( f1, f2 )     => getEqualityPairs( f1, pol ) ++ getEqualityPairs( f2, pol )
    case Imp( f1, f2 )    => getEqualityPairs( f1, !pol ) ++ getEqualityPairs( f2, pol )
  }

}
