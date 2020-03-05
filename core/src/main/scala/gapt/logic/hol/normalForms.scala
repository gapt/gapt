package gapt.logic.hol

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Atom
import gapt.expr.formula.Bottom
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.Quant
import gapt.expr.formula.Top
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.hol.containsStrongQuantifier
import gapt.logic.Polarity
import gapt.proofs.FOLClause
import gapt.proofs.HOLClause
import gapt.proofs.Sequent
import gapt.proofs.resolution.Input
import gapt.proofs.resolution.structuralCNF

/**
 * Transforms a formula to negation normal form (transforming also
 * implications into disjunctions)
 */
object toNNF {
  def apply( f: Formula ): Formula = f match {
    case Top() | Bottom() => f
    case Atom( _, _ )     => f
    case Imp( f1, f2 )    => Or( toNNF( Neg( f1 ) ), toNNF( f2 ) )
    case And( f1, f2 )    => And( toNNF( f1 ), toNNF( f2 ) )
    case Or( f1, f2 )     => Or( toNNF( f1 ), toNNF( f2 ) )
    case Ex( x, f )       => Ex( x, toNNF( f ) )
    case All( x, f )      => All( x, toNNF( f ) )
    case Neg( f ) => f match {
      case Top()         => Bottom()
      case Bottom()      => Top()
      case Atom( _, _ )  => Neg( f )
      case Neg( f1 )     => toNNF( f1 )
      case Imp( f1, f2 ) => And( toNNF( f1 ), toNNF( Neg( f2 ) ) )
      case And( f1, f2 ) => Or( toNNF( Neg( f1 ) ), toNNF( Neg( f2 ) ) )
      case Or( f1, f2 )  => And( toNNF( Neg( f1 ) ), toNNF( Neg( f2 ) ) )
      case Ex( x, f )    => All( x, toNNF( Neg( f ) ) )
      case All( x, f )   => Ex( x, toNNF( Neg( f ) ) )
      case _             => throw new Exception( "ERROR: Unexpected case while transforming to negation normal form." )
    }
    case _ => throw new Exception( "ERROR: Unexpected case while transforming to negation normal form." )
  }

  def apply( f: FOLFormula ): FOLFormula = apply( f.asInstanceOf[Formula] ).asInstanceOf[FOLFormula]
}

/**
 * Simplify a Formula using the equations for bottom and top as
 * well as idempotence of conjunction and disjunction.
 */
object simplifyPropositional {
  def apply( f: Formula ): Formula = f match {
    case And( l, r ) => ( simplifyPropositional( l ), simplifyPropositional( r ) ) match {
      case ( Top(), r )       => r
      case ( r, Top() )       => r
      case ( Bottom(), _ )    => Bottom()
      case ( _, Bottom() )    => Bottom()
      case ( l, r ) if l == r => l
      case ( l, r )           => And( l, r )
    }
    case Or( l, r ) => ( simplifyPropositional( l ), simplifyPropositional( r ) ) match {
      case ( Top(), _ )       => Top()
      case ( _, Top() )       => Top()
      case ( Bottom(), r )    => r
      case ( r, Bottom() )    => r
      case ( l, r ) if l == r => l
      case ( l, r )           => Or( l, r )
    }
    case Imp( l, r ) => ( simplifyPropositional( l ), simplifyPropositional( r ) ) match {
      case ( Top(), r )       => r
      case ( _, Top() )       => Top()
      case ( Bottom(), _ )    => Top()
      case ( r, Bottom() )    => simplifyPropositional( Neg( r ) )
      case ( l, r ) if l == r => Top()
      case ( l, r )           => Imp( l, r )
    }
    case Neg( s ) => simplifyPropositional( s ) match {
      case Top()    => Bottom()
      case Bottom() => Top()
      case s        => Neg( s )
    }
    case Quant( x, g, isAll ) =>
      simplifyPropositional( g ) match {
        case Top()    => Top()
        case Bottom() => Bottom()
        case g_       => Quant( x, g_, isAll )
      }
    case _ => f
  }

  def apply( f: FOLFormula ): FOLFormula = apply( f.asInstanceOf[Formula] ).asInstanceOf[FOLFormula]
}

/**
 * Computes a positive CNF of a formula, i.e. one that is logically equivalent
 * to the input formula.
 *
 * The computation is done by expanding the input formula using distributivity.
 */
object CNFp {
  def apply( f: FOLFormula ): Set[FOLClause] = apply( f: Formula ).asInstanceOf[Set[FOLClause]]
  def apply( f: Formula ): Set[HOLClause] = {
    require( !containsStrongQuantifier( f, Polarity.Negative ), s"Formula contains strong quantifiers: $f" )
    structuralCNF.onProofs( Seq( Input( Sequent() :+ f ) ), propositional = false, structural = false ).
      map( _.conclusion.map( _.asInstanceOf[Atom] ) )
  }
}

/**
 * Computes a negative CNF of a formula, i.e. one that is logically equivalent
 * to the negation of the input formula.
 *
 * The computation is done by expanding the input formula using distributivity.
 */
object CNFn {
  def apply( f: FOLFormula ): Set[FOLClause] = apply( f: Formula ).asInstanceOf[Set[FOLClause]]
  def apply( f: Formula ): Set[HOLClause] = CNFp( -f )
}

/**
 * Computes a positive DNF of a formula, i.e. one that is logically equivalent
 * to the input formula.
 *
 * The computation is done by expanding the input formula using distributivity.
 */
object DNFp {
  def apply( f: FOLFormula ): Set[FOLClause] = apply( f: Formula ).asInstanceOf[Set[FOLClause]]
  def apply( f: Formula ): Set[HOLClause] = CNFn( f ).map( _.swapped )
}

/**
 * Computes a negative DNF of a formula, i.e. one that is logically equivalent
 * to the negation of the input formula.
 *
 * The computation is done by expanding the input formula using distributivity.
 */
object DNFn {
  def apply( f: FOLFormula ): Set[FOLClause] = apply( f: Formula ).asInstanceOf[Set[FOLClause]]
  def apply( f: Formula ): Set[HOLClause] = CNFp( f ).map( _.swapped )
}

