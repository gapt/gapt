package at.logic.gapt.expr.hol

import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ FOLClause, HOLClause }
import at.logic.gapt.utils.dssupport.ListSupport

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
 *
 * Quantifiers are removed in the process.
 */
object CNFp {
  def apply( f: HOLFormula ): List[List[HOLFormula]] = f match {
    case Bottom()        => List( List() )
    case Top()           => List()
    case HOLAtom( _, _ ) => List( List( f ) )
    case Neg( f1 )       => CNFn( f1 )
    case And( f1, f2 )   => apply( f1 ) ++ apply( f2 )
    case Or( f1, f2 )    => ListSupport.times( apply( f1 ), apply( f2 ) )
    case Imp( f1, f2 )   => ListSupport.times( CNFn( f1 ), apply( f2 ) )
    case All( _, f1 )    => apply( f1 )
    case Ex( _, f1 )     => apply( f1 )
    case _               => throw new IllegalArgumentException( "unknown head of formula: " + f.toString )
  }

  def toClauseList( f: HOLFormula ): List[HOLClause] = {
    apply( f ).distinct.map(
      literals => {
        val neg = literals.filter( isNeg( _ ) ).map( removeNeg( _ ) ).map( _.asInstanceOf[HOLAtom] )
        val pos = literals.filterNot( isNeg( _ ) ).map( _.asInstanceOf[HOLAtom] )
        HOLClause( neg, pos )
      }
    )
  }

  def toClauseList( f: FOLFormula ): List[FOLClause] = toClauseList( f.asInstanceOf[HOLFormula] ).asInstanceOf[List[FOLClause]]

  def toFormulaList( f: HOLFormula ): List[HOLFormula] = apply( f ).map( Or( _ ) )

  def toFormula( f: HOLFormula ): HOLFormula = And( toFormulaList( f ) )
  def toFormula( f: FOLFormula ): FOLFormula = toFormula( f.asInstanceOf[HOLFormula] ).asInstanceOf[FOLFormula]
}

/**
 * Computes a negative CNF of a formula, i.e. one that is logically equivalent
 * to the negation of the input formula.
 *
 * The computation is done by expanding the input formula using distributivity.
 *
 * Quantifiers are removed in the process.
 */
object CNFn {
  def apply( f: HOLFormula ): List[List[HOLFormula]] = f match {
    case Bottom()        => List()
    case Top()           => List( List() )
    case HOLAtom( _, _ ) => List( List( Neg( f ) ) )
    case Neg( f1 )       => CNFp( f1 )
    case And( f1, f2 )   => ListSupport.times( apply( f1 ), apply( f2 ) )
    case Or( f1, f2 )    => apply( f1 ) ++ apply( f2 )
    case Imp( f1, f2 )   => CNFp( f1 ) ++ apply( f2 )
    case All( _, f1 )    => apply( f1 )
    case Ex( _, f1 )     => apply( f1 )
    case _               => throw new IllegalArgumentException( "unknown head of formula: " + f.toString )
  }

  def toFClauseList( f: HOLFormula ): List[HOLClause] = {
    apply( f ).distinct.map(
      literals => {
        val neg = literals.filter( isNeg( _ ) ).map( removeNeg( _ ) ).map( _.asInstanceOf[HOLAtom] )
        val pos = literals.filterNot( isNeg( _ ) ).map( _.asInstanceOf[HOLAtom] )
        HOLClause( neg, pos )
      }
    )
  }

  def toClauseList( f: FOLFormula ): List[FOLClause] = toFClauseList( f.asInstanceOf[HOLFormula] ).asInstanceOf[List[FOLClause]]

  def toFormulaList( f: HOLFormula ): List[HOLFormula] = apply( f ).map( Or( _ ) )

  def toFormula( f: HOLFormula ): HOLFormula = And( toFormulaList( f ) )
}

/**
 * Computes a positive DNF of a formula, i.e. one that is logically equivalent
 * to the input formula.
 *
 * The computation is done by expanding the input formula using distributivity.
 *
 * Quantifiers are removed in the process.
 */
object DNFp {
  def toFormulaList( f: HOLFormula ): List[HOLFormula] = CNFn.toFormulaList( f ).map( dualize( _ ) )
  def toFormulaList( f: FOLFormula ): List[FOLFormula] = toFormulaList( f.asInstanceOf[HOLFormula] ).asInstanceOf[List[FOLFormula]]

  def toFormula( f: HOLFormula ): HOLFormula = Or( toFormulaList( f ) )
}

/**
 * Computes a negative DNF of a formula, i.e. one that is logically equivalent
 * to the negation of the input formula.
 *
 * The computation is done by expanding the input formula using distributivity.
 *
 * Quantifiers are removed in the process.
 */
object DNFn {
  def toFormula( f: HOLFormula ): HOLFormula = dualize( CNFp.toFormula( f ) )
}

