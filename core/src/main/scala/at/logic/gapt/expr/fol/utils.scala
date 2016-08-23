/**
 * Utility functions for first-order logic.
 */

package at.logic.gapt.expr.fol

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.containsQuantifier
import at.logic.gapt.proofs.HOLSequent
import scala.collection.{ GenTraversable, mutable }

object isFOLFunction {
  /** Returns whether t is a function. */
  def apply( t: FOLTerm ): Boolean = apply( t, _ => true )

  /** Returns whether t is a function whose name fulfills to a given condition. */
  def apply( t: FOLTerm, cond: String => Boolean ): Boolean = t match {
    case FOLFunction( f, _ ) => cond( f.toString )
    case _                   => false
  }
}

/** Unsafely extracts the function name from a term. Fails if the term is not a function. */
object FOLFunctionName {
  def apply( t: FOLTerm ) = t match { case FOLFunction( f, _ ) => f }
}

/** Unsafely extracts the function arguments from a term. Fails if the term is not a function. */
object FOLFunctionArgs {
  def apply( t: FOLTerm ) = t match { case FOLFunction( _, a ) => a }
}

/**
 * Generation of first-order subterms (note that this notion differs from
 * lambda subterms).
 */
object folSubTerms {
  def apply( t: LambdaExpression ): Set[LambdaExpression] = apply( Some( t ) )

  def apply( language: Traversable[LambdaExpression] ): Set[LambdaExpression] = {
    val subTerms = mutable.Set[LambdaExpression]()
    for ( t <- language ) walk( t, subTerms )
    subTerms.toSet
  }

  def apply( t: FOLTerm ): Set[FOLTerm] = apply( Some( t ) )

  def apply( language: Traversable[FOLTerm] )( implicit dummyImplicit: DummyImplicit ): Set[FOLTerm] =
    apply( language: Traversable[LambdaExpression] ).asInstanceOf[Set[FOLTerm]]

  private def walk( term: LambdaExpression, subterms: mutable.Set[LambdaExpression] ): Unit =
    // if the term is not in the set of subterms yet, add it and add all its subterms
    // this check avoids duplicate addition of all subterms of a subterm
    if ( !subterms.contains( term ) ) {
      subterms += term
      val Apps( _, args ) = term
      args.foreach( walk( _, subterms ) )
    }

}

object Numeral {
  def apply( k: Int ): FOLTerm = k match {
    case 0 => FOLFunction( "0" )
    case _ => FOLFunction( "s", Numeral( k - 1 ) )
  }

  def unapply( t: FOLTerm ): Option[Int] = t match {
    case FOLFunction( "s", List( Numeral( k ) ) ) => Some( k + 1 )
    case FOLFunction( "0", List() )               => Some( 0 )
    case _                                        => None
  }
}

object isFOLPrenexSigma1 {
  def apply( f: LambdaExpression ): Boolean = f match {
    case Ex.Block( _, matrix: FOLFormula ) if !containsQuantifier( matrix ) => true
    case _ => false
  }

  def apply( seq: HOLSequent ): Boolean =
    seq.antecedent.forall( isFOLPrenexPi1( _ ) ) && seq.succedent.forall( isFOLPrenexSigma1( _ ) )
}

object isFOLPrenexPi1 {
  def apply( f: LambdaExpression ): Boolean = f match {
    case All.Block( _, matrix: FOLFormula ) if !containsQuantifier( matrix ) => true
    case _ => false
  }
}

object Utils {
  // Constructs the FOLTerm f^k(a)
  def iterateTerm( a: FOLTerm, f: String, k: Int ): FOLTerm =
    if ( k < 0 ) throw new Exception( "iterateTerm called with negative iteration count" )
    else if ( k == 0 ) a
    else FOLFunction( f, iterateTerm( a, f, k - 1 ) :: Nil )

  // Constructs the FOLTerm s^k(0)
  def numeral( k: Int ) = Numeral( k )
}

object getArityOfConstants {
  /**
   * Get the constants and their arity from a given formula
   * @param t the FOL expression from which we want to extract
   * @return a set of pairs (arity, name)
   */
  def apply( t: FOLExpression ): Set[( Int, String )] = t match {
    case FOLConst( s )          => Set( ( 0, s ) )
    case FOLVar( _ )            => Set[( Int, String )]()
    case FOLAtom( h, args )     => Set( ( args.length, h.toString ) ) ++ args.map( arg => getArityOfConstants( arg ) ).flatten
    case FOLFunction( h, args ) => Set( ( args.length, h.toString ) ) ++ args.map( arg => getArityOfConstants( arg ) ).flatten

    case And( x, y )            => getArityOfConstants( x ) ++ getArityOfConstants( y )
    case Eq( x, y )             => getArityOfConstants( x ) ++ getArityOfConstants( y )
    case Or( x, y )             => getArityOfConstants( x ) ++ getArityOfConstants( y )
    case Imp( x, y )            => getArityOfConstants( x ) ++ getArityOfConstants( y )
    case Neg( x )               => getArityOfConstants( x )
    case Ex( x, f )             => getArityOfConstants( f )
    case All( x, f )            => getArityOfConstants( f )
  }
}

/**
 * Matcher for Sigma,,n,,
 * A FOLFormula f will match Sigma(k) if f is Sigma,,k,,, but not Sigma,,k-1,,.
 */
object Sigma {
  def unapply( f: FOLFormula ): Option[Int] = f match {
    case FOLAtom( _, _ ) => Some( 0 )
    case Neg( g )        => unapply( g )
    case And( g, h )     => Some( Math.max( unapply( g ).get, unapply( h ).get ) )
    case Or( g, h )      => Some( Math.max( unapply( g ).get, unapply( h ).get ) )
    case Imp( g, h )     => Some( Math.max( unapply( g ).get, unapply( h ).get ) )
    case Ex.Block( vars, g ) =>
      g match {
        case Pi( i ) => Some( i + 1 )
      }
  }
}

/**
 * Matcher for Pi,,n,,
 * A FOLFormula f will match Pi(k) if f is Pi,,k,,, but not Pi,,k-1,,.
 */
object Pi {
  def unapply( f: FOLFormula ): Option[Int] = f match {
    case FOLAtom( _, _ ) => Some( 0 )
    case Neg( g )        => unapply( g )
    case And( g, h )     => Some( Math.max( unapply( g ).get, unapply( h ).get ) )
    case Or( g, h )      => Some( Math.max( unapply( g ).get, unapply( h ).get ) )
    case Imp( g, h )     => Some( Math.max( unapply( g ).get, unapply( h ).get ) )
    case All.Block( _, g ) => g match {
      case Sigma( i ) => Some( i + 1 )
    }
  }
}

/**
 * Matcher for Delta,,n,,
 * A FOLFormula f will match Delta(k) if it is both Sigma,,k,, and Pi,,k,,, but not Sigma,,k-1,, or Pi,,k-1,,.
 */
object Delta {
  def unapply( f: FOLFormula ): Option[Int] = f match {
    case Sigma( k ) => f match {
      case Pi( j ) => Some( Math.min( k, j ) )
    }
  }
}

trait CountingFormulas {
  def exactly: {
    def noneOf( fs: Seq[HOLFormula] ): HOLFormula
    def oneOf( fs: Seq[HOLFormula] ): HOLFormula
  }
  def atMost: {
    def oneOf( fs: Seq[HOLFormula] ): HOLFormula
  }
}

object thresholds extends CountingFormulas {

  object exactly {

    def noneOf( fs: Seq[HOLFormula] ): HOLFormula = -Or( fs )

    def oneOf( fs: Seq[HOLFormula] ): HOLFormula = fs match {
      case Seq()    => Bottom()
      case Seq( f ) => f
      case _ =>
        val ( a, b ) = fs.splitAt( fs.size / 2 )
        ( noneOf( a ) & oneOf( b ) ) | ( oneOf( a ) & noneOf( b ) )
    }

  }

  object atMost {

    def oneOf( fs: Seq[HOLFormula] ): HOLFormula = fs match {
      case Seq() | Seq( _ ) => Top()
      case _ =>
        val ( a, b ) = fs.splitAt( fs.size / 2 )
        ( exactly.noneOf( a ) & atMost.oneOf( b ) ) | ( atMost.oneOf( a ) & exactly.noneOf( b ) )
    }

  }

}

object naive extends CountingFormulas {

  object exactly {

    def noneOf( fs: Seq[HOLFormula] ): HOLFormula = -Or( fs )

    def oneOf( fs: Seq[HOLFormula] ): HOLFormula = Or( fs ) & atMost.oneOf( fs )

  }

  object atMost {

    def oneOf( fs: Seq[HOLFormula] ): HOLFormula = And( for ( a <- fs; b <- fs if a != b ) yield -a | -b )

  }

}
