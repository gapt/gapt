/**
 * Utility functions for first-order logic.
 */

package at.logic.gapt.expr.fol

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.HOLPosition
import scala.collection.mutable

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

// Transforms a formula to negation normal form (transforming also
// implications into disjunctions)
object toNNF {
  def apply( f: FOLFormula ): FOLFormula = f match {
    case Top() | Bottom()    => f
    case FOLAtom( _, _ )     => f
    case FOLFunction( _, _ ) => f
    case Imp( f1, f2 )       => Or( toNNF( Neg( f1 ) ), toNNF( f2 ) )
    case And( f1, f2 )       => And( toNNF( f1 ), toNNF( f2 ) )
    case Or( f1, f2 )        => Or( toNNF( f1 ), toNNF( f2 ) )
    case Ex( x, f )          => Ex( x, toNNF( f ) )
    case All( x, f )         => All( x, toNNF( f ) )
    case Neg( f ) => f match {
      case Top()               => Bottom()
      case Bottom()            => Top()
      case FOLAtom( _, _ )     => Neg( f )
      case FOLFunction( _, _ ) => Neg( f )
      case Neg( f1 )           => toNNF( f1 )
      case Imp( f1, f2 )       => And( toNNF( f1 ), toNNF( Neg( f2 ) ) )
      case And( f1, f2 )       => Or( toNNF( Neg( f1 ) ), toNNF( Neg( f2 ) ) )
      case Or( f1, f2 )        => And( toNNF( Neg( f1 ) ), toNNF( Neg( f2 ) ) )
      case Ex( x, f )          => All( x, toNNF( Neg( f ) ) )
      case All( x, f )         => Ex( x, toNNF( Neg( f ) ) )
      case _                   => throw new Exception( "ERROR: Unexpected case while transforming to negation normal form." )
    }
    case _ => throw new Exception( "ERROR: Unexpected case while transforming to negation normal form." )
  }
}

object toCNF {
  // Assumes f is in NNF
  def apply( f: FOLFormula ): List[FOLFormula] = f match {
    case Top()                   => Nil
    case Bottom()                => List( f )
    case FOLAtom( _, _ )         => List( f )
    case Neg( FOLAtom( _, _ ) )  => List( f )
    case And( f1, f2 )           => toCNF( f1 ) ++ toCNF( f2 )
    case Or( f1, And( f2, f3 ) ) => toCNF( Or( f1, f2 ) ) ++ toCNF( Or( f1, f3 ) )
    case Or( And( f1, f2 ), f3 ) => toCNF( Or( f1, f3 ) ) ++ toCNF( Or( f2, f3 ) )
    case Or( f1, f2 ) =>
      val clauses1 = toCNF( f1 )
      val clauses2 = toCNF( f2 )
      for ( c1 <- clauses1; c2 <- clauses2 ) yield Or( c1, c2 )
    case _ => throw new Exception( "ERROR on CNF transformation of the formula: " + f )
  }
}

object toDNF {
  // Assumes f is in NNF
  def apply( f: FOLFormula ): List[FOLFormula] = f match {
    case Bottom()                => Nil
    case Top()                   => List( f )
    case FOLAtom( _, _ )         => List( f )
    case Neg( FOLAtom( _, _ ) )  => List( f )
    case Or( f1, f2 )            => toDNF( f1 ) ++ toDNF( f2 )
    case And( f1, Or( f2, f3 ) ) => toDNF( And( f1, f2 ) ) ++ toDNF( And( f1, f3 ) )
    case And( Or( f1, f2 ), f3 ) => toDNF( And( f1, f3 ) ) ++ toDNF( And( f2, f3 ) )
    case And( f1, f2 ) =>
      val clauses1 = toDNF( f1 )
      val clauses2 = toDNF( f2 )
      for ( c1 <- clauses1; c2 <- clauses2 ) yield And( c1, c2 )
    case _ => throw new Exception( "ERROR on DNF transformation of the formula: " + f )
  }
}

// Transforms a list of literals into an implication formula, with negative 
// literals on the antecedent and positive literals on the succedent.
object reverseCNF {
  def apply( f: List[FOLFormula] ): FOLFormula = {
    val ( ant, succ ) = f.foldRight( ( List[FOLFormula](), List[FOLFormula]() ) ) {
      case ( f, ( ant, succ ) ) => f match {
        case Neg( a ) => ( a :: ant, succ )
        case a        => ( ant, a :: succ )
      }
    }
    val conj = And( ant )
    val disj = Or( succ )
    Imp( conj, disj )
  }
}

object Utils {
  // Constructs the FOLTerm f^k(a)
  def iterateTerm( a: FOLTerm, f: String, k: Int ): FOLTerm =
    if ( k < 0 ) throw new Exception( "iterateTerm called with negative iteration count" )
    else if ( k == 0 ) a
    else FOLFunction( f, iterateTerm( a, f, k - 1 ) :: Nil )

  // Constructs the FOLTerm s^k(0)
  def numeral( k: Int ) = iterateTerm( FOLConst( "0" ).asInstanceOf[FOLTerm], "s", k )

  /**
   * A method for generating all subterms of a particular term
   * @param term term, which is processed
   * @param subterms [optional] for speeding up the process, if there are already some computed subterms (default: {})
   * @return a HasMap of all subterms represented as string => subterm
   */
  def st( term: FOLTerm, subterms: mutable.Set[FOLTerm] = mutable.Set[FOLTerm]() ): mutable.Set[FOLTerm] = {
    // if the term is not in the set of subterms yet
    // add it and add all its subterms
    if ( !subterms.contains( term ) ) {
      // add a term
      subterms += term
      // generate all subterms
      val ts = term match {
        case FOLVar( v )            => Set[FOLTerm]()
        case FOLConst( c )          => Set[FOLTerm]()
        case FOLFunction( f, args ) => args.flatMap( ( ( t: FOLTerm ) => st( t, subterms ) ) )
      }
      subterms ++= ts
    }
    subterms
  }

  /**
   * Generating all subterms of a language of FOLTerms
   *
   * @param language termset for which st is called for each element
   * @return list of all subterms
   */
  def subterms( language: List[FOLTerm] ): Set[FOLTerm] = {
    val terms = mutable.Set[FOLTerm]()
    // for each term of the language
    for ( t <- language ) {
      // if terms does not contain t yet
      if ( !terms.contains( t ) ) {
        // add it and all of its subterms to the list
        terms ++= st( t, terms )
      }
    }
    terms.toSet
  }

  /**
   * Calculates the characteristic partition of a term t
   * as described in Eberhard [2014], w.r.t. a non-terminal
   *
   * @param t term for which the characteristic Partition is calculated
   * @return characteristic partition of t
   */
  def calcCharPartition( t: FOLTerm ): List[List[HOLPosition]] = {
    val positions = HOLPosition.getPositions( t, _.isInstanceOf[FOLTerm] ).map( p => p -> t( p ).asInstanceOf[FOLTerm] )
    /**
     * It recursively separates the positions in the list into different
     * partitions accorindg to their referencing terms.
     *
     * @param pos position list
     * @return
     */
    def recCCP( pos: List[( HOLPosition, FOLTerm )] ): List[List[HOLPosition]] = {
      pos match {
        case x :: xs => {
          val result = ( ( None, Some( x._1 ) ) :: xs.foldLeft( List[( Option[( HOLPosition, FOLTerm )], Option[HOLPosition] )]() )( ( acc, y ) => {
            // add them to the characteristic Partition if the terms match
            if ( x._2 == y._2 ) {
              ( None, Some( y._1 ) ) :: acc
            } else {
              ( Some( y ), None ) :: acc
            }
          } ) )
          val furtherPositions = result.unzip._1.flatten
          result.unzip._2.flatten :: recCCP( furtherPositions ) // get rid of the option and concatenate with the lists of positions except the ones we just added to the current partition
        }
        case _ => Nil // if no positions are left
      }
    }
    return recCCP( positions )
  }

  /**
   * Provided a FOLTerm, the function replaces each occurrence of a FOLVar starting with
   * prefix1, by a FOLVar starting with prefix2 instead.
   *
   * @param t the FOLTerm which should be processed
   * @param prefix1 prefix we are looking for in t
   * @param prefix2 prefix which should replace prefix1
   * @return a FOLTerm, where all FOLVars starting with prefix1 have been replaced by FOLVars starting with prefix2 instead
   */
  def replaceAlls( t: FOLTerm, prefix1: String, prefix2: String ): FOLTerm = {
    t match {
      case FOLVar( x )         => FOLVar( x.replace( prefix1, prefix2 ) )
      case FOLConst( c )       => FOLConst( c )
      case FOLFunction( f, l ) => FOLFunction( f, l.map( p => replaceAlls( p, prefix1, prefix2 ) ) )
      case _                   => throw new Exception( "Unexpected case. Malformed FOLTerm." )
    }
  }

  /**
   * increments the index of a FOLVar by 1, if it has an index
   * otherwise do nothing
   *
   * @param v FOLVar to be processed
   * @return v with incremented index
   */
  def incrementIndex( v: FOLVar ): FOLVar = {
    val parts = v.toString.split( "_" )
    try {
      val index = parts.last.toInt
      FOLVar( ( parts.take( parts.size - 1 ).foldLeft( "" )( ( acc, x ) => acc + "_" + x ) + "_" + ( index + 1 ) ).substring( 1 ) )
    } catch {
      case e: NumberFormatException => return v //variable has no index
    }
  }

  /**
   * for a particular term increment all variables indexes
   * which start with provided prefix
   *
   * @param t term
   * @return term with incremented variable indexes
   */
  def incrementAlls( t: FOLTerm, prefix: String ): FOLTerm = {
    t match {
      case FOLVar( x ) if x.startsWith( prefix ) => incrementIndex( FOLVar( x ) )
      case FOLVar( x )                           => FOLVar( x )
      case FOLConst( c )                         => FOLConst( c )
      case FOLFunction( f, l )                   => FOLFunction( f, l.map( p => incrementAlls( p, prefix ) ) )
      case _                                     => throw new Exception( "Unexpected case. Malformed FOLTerm." )
    }
  }

  /**
   * Checks if a FOLVar exists in t with a certain variable_prefix.
   * e.g. nonterminalOccurs(f(x1,y2,z1), "y") = true
   *
   * @param t term
   * @param variable_prefix variable prefix
   * @return true if a variable with the particular prefix exists in t, otherwise false
   */
  def nonterminalOccurs( t: FOLTerm, variable_prefix: String ): Boolean = t match {
    case FOLVar( x )            => return x.startsWith( variable_prefix )
    case FOLConst( x )          => false
    case FOLFunction( x, args ) => return args.foldLeft( false )( ( s, a ) => s || nonterminalOccurs( a, variable_prefix ) )
    case _                      => return false
  }

  /**
   * If for a given term t, the termposition position exists
   * replace the subtree with the root at position with a FOLVar(variable_index).
   * Otherwise return the term as it is.
   *
   * @param t term
   * @param variable string representation of the nonterminal prefix
   * @param position list of positions of variable
   * @param index nonterminal index i
   * @return the original term if the replacement could not be processed, or t|p = α_index
   */
  def replaceAtPosition( t: FOLTerm, variable: String, position: HOLPosition, index: Int ): FOLTerm =
    HOLPosition.toLambdaPositionOption( t )( position ) match {
      case Some( p ) => LambdaPosition.replace( t, p, FOLVar( variable + "_" + index ) ).asInstanceOf[FOLTerm]
      case _         => t
    }

  /**
   * Given a FOLTerm and a prefix for a variable,
   * this function returns a list of all FOLVars in t starting
   * with the particular prefix
   *
   * @param t FOLTerm
   * @param nonterminal_prefix prefix of non-terminals
   * @return a list of strings representing all non-terminals in t
   */
  def getNonterminals( t: FOLTerm, nonterminal_prefix: String ): List[String] = {
    val s = t match {
      case FOLFunction( f, args ) => args.foldLeft( Set[String]() )( ( prevargs, arg ) => prevargs ++ getNonterminals( arg, nonterminal_prefix ) )
      case FOLVar( v )            => if ( v.toString.startsWith( nonterminal_prefix ) ) Set[String]( v.toString() ) else Set[String]()
      case _                      => Set[String]()
    }
    s.toList
  }

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
