package gapt.proofs.expansion

import gapt.expr._
import gapt.expr.hol.instantiate
import gapt.proofs.HOLSequent

object formulaToExpansionTree {
  def apply( sequent: HOLSequent ): ExpansionSequent =
    for ( ( f, i ) <- sequent.zipWithIndex ) yield formulaToExpansionTree( f, i.polarity )

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
          map {
            case ( ev: Var, insts ) => ETStrongQuantifier( formula, ev, conv( instantiate( formula, ev ), f, insts, pol ) )
            case ( res, insts )     => throw new IllegalArgumentException( s"Substitution maps variable ${insts.head( v )} to non-variable $res" )
          } )
    }
}

object numberOfInstancesET {
  def apply( t: ExpansionTree ): Int =
    t.treeLike.postOrder collect { case ETWeakQuantifier( _, instances ) => instances.size } sum
  def apply( s: ExpansionSequent ): Int = s.elements map apply sum
  def apply( ep: ExpansionProof ): Int = apply( ep.expansionSequent )
}