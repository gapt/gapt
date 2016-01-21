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
object FOLSubTerms {
  /**
   * Generate all subterms of a FOLTerm.
   */
  def apply( t: FOLTerm ): Set[FOLTerm] = {
    val subterms = mutable.Set[FOLTerm]()
    apply_( t, subterms )
    subterms.toSet
  }

  /**
   * Generate all subterms of a list of FOLTerms.
   */
  def apply( language: GenTraversable[FOLTerm] ): Set[FOLTerm] = {
    val subterms = mutable.Set[FOLTerm]()
    language.foreach( apply_( _, subterms ) )
    subterms.toSet
  }

  /**
   * Generate all subterms of a FOLTerm using a mutable set for efficiency.
   * @param term term, which is processed
   * @param subterms for speeding up the process, if there are already some computed subterms
   * @return the set of all first-order subterms of term
   */
  private def apply_( term: FOLTerm, subterms: mutable.Set[FOLTerm] ): Unit = {
    // if the term is not in the set of subterms yet, add it and add all its subterms
    // this check avoids duplicate addition of all subterms of a subterm
    if ( !subterms.contains( term ) ) {
      subterms += term
      term match {
        case FOLFunction( _, args ) => args.foreach( apply_( _, subterms ) )
      }
    }
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

object toAbbreviatedString {
  /**
   * This function takes a FOL construction and converts it to a abbreviated string version. The abbreviated string version is made
   * by replacing the code construction for logic symbols by string versions in the file expr/hol/logicSymbols.scala.
   * Several recursive function calls will be transformed into an abbreviated form (e.g. f(f(f(x))) => f^3^(x)).
   * Terms are also handled by the this function.
   *
   * @param  e  The method has no parameters other then the object which is to be written as a string
   *
   * @throws Exception This occurs when an unknown subformula is found when parsing the FOL construction
   *
   * @return A String which contains the defined symbols in expr/hol/logicSymbols.scala.
   *
   */
  def apply( e: FOLExpression ): String = {

    val p = pretty( e )

    val r: String = e match {
      case FOLFunction( x, args ) => {
        if ( p._1 != p._2 && p._2 != "tuple1" )
          if ( p._3 > 0 )
            return p._2 + "^" + ( p._3 + 1 ) + "(" + p._1 + ") "
          else
            return p._1
        else
          return p._1
      }
      case _ => return p._1
    }

    return r
  }

  private def pretty( exp: FOLExpression ): ( String, String, Int ) = {

    val s: ( String, String, Int ) = exp match {
      case null        => ( "null", "null", -2 )
      case FOLVar( x ) => ( x.toString(), x.toString(), 0 )
      case FOLAtom( x, args ) => {
        ( x.toString() + "(" + ( args.foldRight( "" ) {
          case ( x, "" )  => "" + toAbbreviatedString( x )
          case ( x, str ) => toAbbreviatedString( x ) + ", " + str
        } ) + ")", x.toString(), 0 )
      }
      case FOLFunction( x, args ) => {
        // if only 1 argument is provided
        // check if abbreviating of recursive function calls is possible
        if ( args.length == 1 ) {
          val p = pretty( args.head )

          // current function is equal to first and ONLY argument
          if ( p._2 == x.toString() ) {
            // increment counter and return (<current-string>, <functionsymbol>, <counter>)
            return ( p._1, x.toString(), p._3 + 1 )
          } // function symbol has changed from next to this level
          else {

            // in case of multiple recursive function calls
            if ( p._3 > 0 ) {
              return ( p._2 + "^" + p._3 + "(" + p._1 + ")", x.toString(), 0 )
            } // otherwise
            else {
              return ( p._1, x.toString(), 1 )
            }
          }
        } else {
          return ( x.toString() + "(" + ( args.foldRight( "" ) {
            case ( x, "" ) => toAbbreviatedString( x )
            case ( x, s )  => toAbbreviatedString( x ) + ", " + s
          } ) + ")", x.toString(), 0 )
        }

      }
      case And( x, y )   => ( "(" + toAbbreviatedString( x ) + " " + AndC.name + " " + toAbbreviatedString( y ) + ")", AndC.name.toString(), 0 )
      case Eq( x, y )    => ( "(" + toAbbreviatedString( x ) + " " + EqC.name + " " + toAbbreviatedString( y ) + ")", EqC.name.toString(), 0 )
      case Or( x, y )    => ( "(" + toAbbreviatedString( x ) + " " + OrC.name + " " + toAbbreviatedString( y ) + ")", OrC.name.toString(), 0 )
      case Imp( x, y )   => ( "(" + toAbbreviatedString( x ) + " " + ImpC.name + " " + toAbbreviatedString( y ) + ")", ImpC.name.toString(), 0 )
      case Neg( x )      => ( NegC.name + toAbbreviatedString( x ), NegC.name.toString(), 0 )
      case Ex( x, f )    => ( ExistsC.name + toAbbreviatedString( x ) + "." + toAbbreviatedString( f ), ExistsC.name.toString(), 0 )
      case All( x, f )   => ( ForallC.name + toAbbreviatedString( x ) + "." + toAbbreviatedString( f ), ForallC.name.toString(), 0 )
      //      case Abs( v, exp )    => ( "(λ" + toAbbreviatedString( v ) + "." + toAbbreviatedString( exp ) + ")", "λ", 0 )
      //      case App( l, r )      => ( "(" + toAbbreviatedString( l ) + ")(" + toAbbreviatedString( r ) + ")", "()()", 0 )
      case FOLConst( x ) => ( x.toString(), x.toString(), 0 )
      case _             => throw new Exception( "ERROR: Unknown FOL expression." );
    }
    return s

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
      println( s"$vars, $g" )
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
    def noneOf( fs: Seq[FOLFormula] ): FOLFormula
    def oneOf( fs: Seq[FOLFormula] ): FOLFormula
  }
  def atMost: {
    def oneOf( fs: Seq[FOLFormula] ): FOLFormula
  }
}

object thresholds extends CountingFormulas {

  object exactly {

    def noneOf( fs: Seq[FOLFormula] ): FOLFormula = -Or( fs )

    def oneOf( fs: Seq[FOLFormula] ): FOLFormula = fs match {
      case Seq()    => Bottom()
      case Seq( f ) => f
      case _ =>
        val ( a, b ) = fs.splitAt( fs.size / 2 )
        ( noneOf( a ) & oneOf( b ) ) | ( oneOf( a ) & noneOf( b ) )
    }

  }

  object atMost {

    def oneOf( fs: Seq[FOLFormula] ): FOLFormula = fs match {
      case Seq() | Seq( _ ) => Top()
      case _ =>
        val ( a, b ) = fs.splitAt( fs.size / 2 )
        ( exactly.noneOf( a ) & atMost.oneOf( b ) ) | ( atMost.oneOf( a ) & exactly.noneOf( b ) )
    }

  }

}

object naive extends CountingFormulas {

  object exactly {

    def noneOf( fs: Seq[FOLFormula] ): FOLFormula = -Or( fs )

    def oneOf( fs: Seq[FOLFormula] ): FOLFormula = Or( fs ) & atMost.oneOf( fs )

  }

  object atMost {

    def oneOf( fs: Seq[FOLFormula] ): FOLFormula = And( for ( a <- fs; b <- fs if a != b ) yield -a | -b )

  }

}
