package gapt.proofs.expansion

import gapt.expr._
import gapt.expr.formula.And
import gapt.expr.formula.Atom
import gapt.expr.formula.Bottom
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.Quant
import gapt.expr.formula.Top
import gapt.expr.subst.Substitution
import gapt.logic.Polarity
import gapt.proofs.HOLSequent

object formulaToExpansionTree {
  def apply( sequent: HOLSequent ): ExpansionSequent =
    for ( ( f, i ) <- sequent.zipWithIndex ) yield formulaToExpansionTree( f, i.polarity )

  def apply( formula: Formula, pol: Polarity ): ExpansionTree =
    apply( formula, Set.empty, pol )

  def apply( formula: Formula, substitutions: Iterable[Substitution], pol: Polarity ): ExpansionTree =
    ExpansionTree( formula, pol, conv( formula, substitutions.toSet, pol ) )

  private def conv( origFormula: Formula, substitutions: Set[Substitution], pol: Polarity ): ETt = origFormula match {
    case _: Atom       => ETtAtom
    case Top()         => ETtNullary
    case Bottom()      => ETtNullary
    case Neg( of )     => ETtUnary( conv( of, substitutions, !pol ) )
    case And( of, og ) => ETtBinary( conv( of, substitutions, pol ), conv( og, substitutions, pol ) )
    case Or( of, og )  => ETtBinary( conv( of, substitutions, pol ), conv( og, substitutions, pol ) )
    case Imp( of, og ) => ETtBinary( conv( of, substitutions, !pol ), conv( og, substitutions, pol ) )
    case Quant( v, f, isAll ) if isAll == pol.inAnt =>
      ETtWeak( Map() ++ substitutions.groupBy( _( v ) ).
        map { case ( term, insts ) => term -> conv( f, insts, pol ) } )
    case Quant( v, f, isAll ) if isAll == pol.inSuc =>
      ETtMerge( substitutions.groupBy( _( v ) ).map {
        case ( ev: Var, insts ) => ETtStrong( ev, conv( f, insts, pol ) )
        case ( res, insts ) =>
          throw new IllegalArgumentException( s"Substitution maps variable ${insts.head( v )} to non-variable $res" )
      } )
  }
}

object numberOfInstancesET {
  def apply( t: ETt ): Int = {
    var result = 0
    t.foreach { case ETtWeak( insts ) => result += insts.size case _ => }
    result
  }
  def apply( t: ExpansionTree ): Int = apply( t.term )
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

  def apply( t: ExpansionTree ): ExpansionTree = ExpansionTree( t.shallow, t.polarity, apply( t.term ) )

  def apply( t: ETt ): ETt = t match {
    case ETtNullary | ETtAtom | ETtWeakening => t
    case ETtMerge( s1, s2 ) => ( apply( s1 ), apply( s2 ) ) match {
      case ( ETtWeakening, r2 ) => r2
      case ( r1, ETtWeakening ) => r1
      case ( r1, r2 )           => ETtMerge( r1, r2 )
    }
    case ETtUnary( s ) => apply( s ) match {
      case ETtWeakening => ETtWeakening
      case r            => ETtUnary( r )
    }
    case ETtBinary( s1, s2 ) => ( apply( s1 ), apply( s2 ) ) match {
      case ( ETtWeakening, ETtWeakening ) => ETtWeakening
      case ( r1, r2 )                     => ETtBinary( r1, r2 )
    }
    case ETtStrong( ev, s ) => apply( s ) match {
      case ETtWeakening => ETtWeakening
      case r            => ETtStrong( ev, r )
    }
    case ETtSkolem( st, s ) => apply( s ) match {
      case ETtWeakening => ETtWeakening
      case r            => ETtSkolem( st, r )
    }
    case ETtWeak( inst ) =>
      val cleanInst =
        for ( ( i, ch ) <- inst; ch_ = apply( ch ) if ch_ != ETtWeakening )
          yield i -> ch_
      if ( cleanInst.isEmpty ) ETtWeakening else ETtWeak( cleanInst )
    case ETtDef( sh, ch ) => apply( ch ) match {
      case ETtWeakening => ETtWeakening
      case ch_          => ETtDef( sh, ch_ )
    }
  }
}

object pushWeakeningsUp {
  def apply( ep: ExpansionProof ): ExpansionProof = ExpansionProof( apply( ep.expansionSequent ) )
  def apply( es: ExpansionSequent ): ExpansionSequent = es.map( apply )

  def apply( et: ExpansionTree ): ExpansionTree = et match {
    case ETAtom( _, _ ) | ETBottom( _ ) | ETTop( _ ) => et
    case ETWeakening( sh, pol )                      => apply( sh, pol )
    case ETMerge( a, b )                             => ETMerge( apply( a ), apply( b ) )
    case ETNeg( a )                                  => ETNeg( apply( a ) )
    case ETAnd( a, b )                               => ETAnd( apply( a ), apply( b ) )
    case ETOr( a, b )                                => ETOr( apply( a ), apply( b ) )
    case ETImp( a, b )                               => ETImp( apply( a ), apply( b ) )
    case ETWeakQuantifier( sh, insts )               => ETWeakQuantifier( sh, Map() ++ insts.view.mapValues( apply ).toMap )
    case ETStrongQuantifier( sh, ev, ch )            => ETStrongQuantifier( sh, ev, apply( ch ) )
    case ETSkolemQuantifier( sh, skT, ch )           => ETSkolemQuantifier( sh, skT, apply( ch ) )
    case ETDefinition( sh, ch )                      => ETDefinition( sh, apply( ch ) )
  }

  def apply( sh: Formula, pol: Polarity ): ExpansionTree = sh match {
    case sh: Atom    => ETAtom( sh, pol )
    case Neg( a )    => ETNeg( apply( a, !pol ) )
    case And( a, b ) => ETAnd( apply( a, pol ), apply( b, pol ) )
    case Or( a, b )  => ETOr( apply( a, pol ), apply( b, pol ) )
    case Imp( a, b ) => ETImp( apply( a, !pol ), apply( b, pol ) )
    case _           => ETWeakening( sh, pol )
  }
}
