package at.logic.gapt.proofs.expansion

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.instantiate

object formulaToExpansionTree {
  def apply( formula: Formula, pol: Polarity ): ExpansionTree =
    conv( formula, formula, Set(), pol )

  def apply( formula: Formula, substitutions: Traversable[_ <: Substitution], pol: Polarity ): ExpansionTree =
    conv( formula, formula, substitutions.toSet, pol )

  private def conv( formula: Formula, origFormula: Formula, substitutions: Set[Substitution], pol: Polarity ): ExpansionTree =
    ( formula, origFormula ) match {
      case ( a: Atom, _ )                 => ETAtom( a, pol )
      case ( Top(), _ )                   => ETTop( pol )
      case ( Bottom(), _ )                => ETBottom( pol )
      case ( Neg( f ), Neg( of ) )        => ETNeg( conv( f, of, substitutions, !pol ) )
      case ( And( f, g ), And( of, og ) ) => ETAnd( conv( f, of, substitutions, pol ), conv( g, og, substitutions, pol ) )
      case ( Or( f, g ), Or( of, og ) )   => ETOr( conv( f, of, substitutions, pol ), conv( g, og, substitutions, pol ) )
      case ( Imp( f, g ), Imp( of, og ) ) => ETImp( conv( f, of, substitutions, !pol ), conv( g, og, substitutions, pol ) )
      case ( _, Quant( v, f, isAll ) ) if isAll == pol.inAnt =>
        ETWeakQuantifier( formula, Map() ++ substitutions.groupBy( _( v ) ).
          map { case ( term, insts ) => term -> conv( instantiate( formula, term ), f, insts, pol ) } )
      case ( _, Quant( v, f, isAll ) ) if isAll == pol.inSuc =>
        ETMerge( formula, pol, substitutions.groupBy( _( v ) ).
          map { case ( ev: Var, insts ) => ETStrongQuantifier( formula, ev, conv( instantiate( formula, ev ), f, insts, pol ) ) } )
    }
}

object numberOfInstancesET {
  def apply( t: ExpansionTree ): Int =
    t.treeLike.postOrder collect { case ETWeakQuantifier( _, instances ) => instances.size } sum
  def apply( s: ExpansionSequent ): Int = s.elements map apply sum
  def apply( ep: ExpansionProof ): Int = apply( ep.expansionSequent )
  def apply( epwc: ExpansionProofWithCut ): Int = apply( epwc.expansionWithCutAxiom )
}