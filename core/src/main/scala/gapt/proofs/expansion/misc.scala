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

/**
 * Extracts all merge ETs from an expansion proof.
 */
object findMerges {
  def apply( t: ExpansionProof ): Set[ExpansionTree] =
    t.subProofs.collect( { case x @ ETMerge( _, _ ) => x } )
}

/**
 * Returns the eigenvariables in an expansion tree or expansion sequent.
 */
object eigenVariablesET {
  def apply( tree: ExpansionTree ): Set[Var] = tree.subProofs collect { case ETStrongQuantifier( _, v, _ ) => v }
  def apply( s: ExpansionSequent ): Set[Var] = s.elements.flatMap { apply }.toSet
}

object isPropositionalET {
  def apply( tree: ExpansionTree ): Boolean =
    tree match {
      case ETWeakening( _, _ ) => true
      case ETMerge( a, b ) => isPropositionalET( a ) && isPropositionalET( b )
      case ETAtom( _, _ ) | ETTop( _ ) | ETBottom( _ ) => true
      case ETNeg( sub ) => isPropositionalET( sub )
      case ETAnd( a, b ) => isPropositionalET( a ) && isPropositionalET( b )
      case ETOr( a, b ) => isPropositionalET( a ) && isPropositionalET( b )
      case ETImp( a, b ) => isPropositionalET( a ) && isPropositionalET( b )
      case ETDefinition( _, sub ) => isPropositionalET( sub )
      case _ => false
    }
}

/**
 * Cleans up an expansion tree by introducing weakenings as late as possible.
 */
object cleanStructureET {
  def apply( es: ExpansionSequent ): ExpansionSequent = es.map( apply )
  def apply( ep: ExpansionProof ): ExpansionProof = ExpansionProof( apply( ep.expansionSequent ) )

  def apply( t: ExpansionTree ): ExpansionTree = t match {
    case ETMerge( s1, s2 ) => ( apply( s1 ), apply( s2 ) ) match {
      case ( ETWeakening( _, _ ), r2 ) => r2
      case ( r1, ETWeakening( _, _ ) ) => r1
      case ( r1, r2 )                  => ETMerge( r1, r2 )
    }
    case ETNeg( s ) => apply( s ) match {
      case ETWeakening( f, p ) => ETWeakening( -f, !p )
      case r                   => ETNeg( r )
    }
    case ETAnd( s1, s2 ) => ( apply( s1 ), apply( s2 ) ) match {
      case ( ETWeakening( f1, p ), ETWeakening( f2, _ ) ) => ETWeakening( f1 & f2, p )
      case ( r1, r2 )                                     => ETAnd( r1, r2 )
    }
    case ETOr( s1, s2 ) => ( apply( s1 ), apply( s2 ) ) match {
      case ( ETWeakening( f1, p ), ETWeakening( f2, _ ) ) => ETWeakening( f1 | f2, p )
      case ( r1, r2 )                                     => ETOr( r1, r2 )
    }
    case ETImp( s1, s2 ) => ( apply( s1 ), apply( s2 ) ) match {
      case ( ETWeakening( f1, _ ), ETWeakening( f2, p ) ) => ETWeakening( f1 --> f2, p )
      case ( r1, r2 )                                     => ETImp( r1, r2 )
    }
    case ETStrongQuantifier( sh, ev, s ) => apply( s ) match {
      case ETWeakening( _, p ) => ETWeakening( sh, p )
      case r                   => ETStrongQuantifier( sh, ev, r )
    }
    case ETSkolemQuantifier( sh, st, sf, s ) => apply( s ) match {
      case ETWeakening( _, p ) => ETWeakening( sh, p )
      case r                   => ETSkolemQuantifier( sh, st, sf, r )
    }
    case ETWeakQuantifier( sh, inst ) =>
      val cleanInst = ( Map() ++ inst.mapValues( apply ) ).
        filter { case ( _, ETWeakening( _, _ ) ) => false case _ => true }
      if ( cleanInst isEmpty ) ETWeakening( sh, t.polarity )
      else ETWeakQuantifier( sh, cleanInst )
    case _ => t
  }
}