package at.logic.gapt.expr.hol

import at.logic.gapt.expr._
import at.logic.gapt.proofs.resolution.{ Input, structuralCNF }
import at.logic.gapt.proofs.{ Clause, FOLClause, HOLClause, Sequent }

/**
 * Transforms a formula to negation normal form (transforming also
 * implications into disjunctions)
 */
object toNNF {
  def apply( f: HOLFormula ): HOLFormula = f match {
    case Top() | Bottom() => f
    case HOLAtom( _, _ )  => f
    case Imp( f1, f2 )    => Or( toNNF( Neg( f1 ) ), toNNF( f2 ) )
    case And( f1, f2 )    => And( toNNF( f1 ), toNNF( f2 ) )
    case Or( f1, f2 )     => Or( toNNF( f1 ), toNNF( f2 ) )
    case Ex( x, f )       => Ex( x, toNNF( f ) )
    case All( x, f )      => All( x, toNNF( f ) )
    case Neg( f ) => f match {
      case Top()           => Bottom()
      case Bottom()        => Top()
      case HOLAtom( _, _ ) => Neg( f )
      case Neg( f1 )       => toNNF( f1 )
      case Imp( f1, f2 )   => And( toNNF( f1 ), toNNF( Neg( f2 ) ) )
      case And( f1, f2 )   => Or( toNNF( Neg( f1 ) ), toNNF( Neg( f2 ) ) )
      case Or( f1, f2 )    => And( toNNF( Neg( f1 ) ), toNNF( Neg( f2 ) ) )
      case Ex( x, f )      => All( x, toNNF( Neg( f ) ) )
      case All( x, f )     => Ex( x, toNNF( Neg( f ) ) )
      case _               => throw new Exception( "ERROR: Unexpected case while transforming to negation normal form." )
    }
    case _ => throw new Exception( "ERROR: Unexpected case while transforming to negation normal form." )
  }

  def apply( f: FOLFormula ): FOLFormula = apply( f.asInstanceOf[HOLFormula] ).asInstanceOf[FOLFormula]
}

/**
 * Simplify a HOLFormula using the equations for bottom and top as
 * well as idempotence of conjunction and disjunction.
 */
object simplify {
  def apply( f: HOLFormula ): HOLFormula = f match {
    case And( l, r ) => ( simplify( l ), simplify( r ) ) match {
      case ( Top(), r )       => r
      case ( r, Top() )       => r
      case ( Bottom(), _ )    => Bottom()
      case ( _, Bottom() )    => Bottom()
      case ( l, r ) if l == r => l
      case ( l, r )           => And( l, r )
    }
    case Or( l, r ) => ( simplify( l ), simplify( r ) ) match {
      case ( Top(), _ )       => Top()
      case ( _, Top() )       => Top()
      case ( Bottom(), r )    => r
      case ( r, Bottom() )    => r
      case ( l, r ) if l == r => l
      case ( l, r )           => Or( l, r )
    }
    case Imp( l, r ) => ( simplify( l ), simplify( r ) ) match {
      case ( Top(), r )       => r
      case ( _, Top() )       => Top()
      case ( Bottom(), _ )    => Top()
      case ( r, Bottom() )    => simplify( Neg( r ) )
      case ( l, r ) if l == r => Top()
      case ( l, r )           => Imp( l, r )
    }
    case Neg( s ) => simplify( s ) match {
      case Top()    => Bottom()
      case Bottom() => Top()
      case s        => Neg( s )
    }
    case _ => f
  }

  def apply( f: FOLFormula ): FOLFormula = apply( f.asInstanceOf[HOLFormula] ).asInstanceOf[FOLFormula]
}

/**
 * Computes a positive CNF of a formula, i.e. one that is logically equivalent
 * to the input formula.
 *
 * The computation is done by expanding the input formula using distributivity.
 */
object CNFp {
  def apply( f: FOLFormula ): Set[FOLClause] = apply( f: HOLFormula ).asInstanceOf[Set[FOLClause]]
  def apply( f: HOLFormula ): Set[HOLClause] = {
    require( !containsStrongQuantifier( f, Polarity.Negative ), s"Formula contains strong quantifiers: $f" )
    structuralCNF.onProofs( Seq( Input( Sequent() :+ f ) ), propositional = false, structural = false ).
      map( _.conclusion.map( _.asInstanceOf[HOLAtom] ) )
  }
}

/**
 * Computes a negative CNF of a formula, i.e. one that is logically equivalent
 * to the negation of the input formula.
 *
 * The computation is done by expanding the input formula using distributivity.
 */
object CNFn {
  def apply( f: FOLFormula ): Set[FOLClause] = apply( f: HOLFormula ).asInstanceOf[Set[FOLClause]]
  def apply( f: HOLFormula ): Set[HOLClause] = CNFp( -f )
}

/**
 * Computes a positive DNF of a formula, i.e. one that is logically equivalent
 * to the input formula.
 *
 * The computation is done by expanding the input formula using distributivity.
 */
object DNFp {
  def apply( f: FOLFormula ): Set[FOLClause] = apply( f: HOLFormula ).asInstanceOf[Set[FOLClause]]
  def apply( f: HOLFormula ): Set[HOLClause] = CNFn( f ).map( _.swapped )
}

/**
 * Computes a negative DNF of a formula, i.e. one that is logically equivalent
 * to the negation of the input formula.
 *
 * The computation is done by expanding the input formula using distributivity.
 */
object DNFn {
  def apply( f: FOLFormula ): Set[FOLClause] = apply( f: HOLFormula ).asInstanceOf[Set[FOLClause]]
  def apply( f: HOLFormula ): Set[HOLClause] = CNFp( f ).map( _.swapped )
}

