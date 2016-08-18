package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.containsQuantifier
import at.logic.gapt.proofs.HOLSequent

/**
 * Builds an expansion tree from a formula and a map from variables to terms.
 * The paremeter pos is true if  the formula is to be considered positive
 * (right side of the sequent).
 */
object formulaToExpansionTree {
  def apply( form: HOLFormula, pos: Polarity ): ExpansionTree = {
    assert( !containsQuantifier( form ) )
    apply( form, List(), pos )
  }

  @deprecated( "Substitute and merge expansion trees instead", "2016-01-13" )
  def apply( form: HOLFormula, subs: List[_ <: Substitution], pos: Polarity ): ExpansionTree = {
    // form's quantified variables must be pairwise distinct
    assert( isInVNF( form ), "formulaToExpansionTree: bound variables are not pairwise distinct." )
    // substitutions should not have variable capture
    assert( subs.forall( s => s.domain intersect s.range isEmpty ), "formulaToExpansionTree: substitutions have variable capture." )
    apply_( form, subs, pos )
  }

  private def apply_( form: HOLFormula, subs: List[_ <: Substitution], pos: Polarity ): ExpansionTree = form match {
    case a: HOLAtom    => ETAtom( a, pos )
    case Neg( f )      => ETNeg( apply_( f, subs, !pos ) )
    case And( f1, f2 ) => ETAnd( apply_( f1, subs, pos ), apply_( f2, subs, pos ) )
    case Or( f1, f2 )  => ETOr( apply_( f1, subs, pos ), apply_( f2, subs, pos ) )
    case Imp( f1, f2 ) => ETImp( apply_( f1, subs, !pos ), apply_( f2, subs, pos ) )
    case All( v, f ) => pos match {
      case Polarity.InSuccedent => // Strong quantifier
        val valid_subs = subs.filter( s => s.domain.contains( v ) )
        assert( valid_subs.length == 1, ( "Found no substitutions for " + v + " in " + subs ) )
        val next_f = valid_subs.head( f )
        val ev = valid_subs.head( v ).asInstanceOf[Var]
        ETStrongQuantifier( form, ev, apply_( next_f, valid_subs, pos ) )
      case Polarity.InAntecedent => // Weak quantifier
        ETWeakQuantifier( form, subs.filter( _.domain.contains( v ) ).groupBy( _( v ) ) map {
          case ( t, subsWithT ) =>
            val next_f = Substitution( v -> t )( f )
            ( t, apply_( next_f, subsWithT, pos ) )
        } )
    }
    case Ex( v, f ) => pos match {
      case Polarity.InSuccedent => // Weak quantifier
        ETWeakQuantifier( form, subs.filter( _.domain.contains( v ) ).groupBy( _( v ) ) map {
          case ( t, subsWithT ) =>
            val next_f = Substitution( v -> t )( f )
            ( t, apply_( next_f, subsWithT, pos ) )
        } )
      case Polarity.InAntecedent => // Strong quantifier
        val valid_subs = subs.filter( s => s.domain.contains( v ) )
        assert( valid_subs.length == 1 )
        val next_f = valid_subs.head( f )
        val ev = valid_subs.head( v ).asInstanceOf[Var]
        ETStrongQuantifier( form, ev, apply_( next_f, valid_subs, pos ) ).asInstanceOf[ExpansionTree]
    }
    case Top()    => ETTop( pos )
    case Bottom() => ETBottom( pos )
    case _        => throw new Exception( "Error transforming a formula into an expansion tree: " + form )
  }
}

object numberOfInstancesET {
  def apply( t: ExpansionTree ): Int =
    t.treeLike.postOrder collect { case ETWeakQuantifier( _, instances ) => instances.size } sum
  def apply( s: ExpansionSequent ): Int = s.elements map apply sum
  def apply( ep: ExpansionProof ): Int = apply( ep.expansionSequent )
  def apply( epwc: ExpansionProofWithCut ): Int = apply( epwc.expansionWithCutAxiom )
}