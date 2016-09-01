
package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol._

/**
 * Given an expansion sequent S which is a tautology modulo symmetry of equality,
 * returns an expansion sequent S' which is S extended by the symmetry instances
 * needed to make it a tautology.
 */
object addSymmetry {

  def apply( s: ExpansionSequent ): ExpansionSequent = {
    val negativePairs = for ( et <- s.elements.view; ETAtom( Eq( l, r ), Polarity.Negative ) <- et.subProofs ) yield l -> r
    val positivePairs = for ( et <- s.elements.view; ETAtom( Eq( l, r ), Polarity.Positive ) <- et.subProofs ) yield l -> r

    positivePairs.map( _.swap ).toSet.intersect( negativePairs.toSet ).
      groupBy( _._1.exptype ).map {
        case ( ty, pairs ) =>
          val Seq( x, y ) = Seq( "x", "y" ).map( Var( _, ty ) )
          val symmAx = hof"!$x !$y ($x=$y -> $y=$x)"
          formulaToExpansionTree(
            symmAx,
            pairs.map { case ( l, r ) => Substitution( x -> l, y -> r ) },
            Polarity.InAntecedent
          )
      } ++: s
  }

}
