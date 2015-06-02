/**
 * Helper functions for first order logic
 */

package at.logic.gapt.language.fol

import at.logic.gapt.expr._
import at.logic.gapt.language.hol.{ getMatrix => getMatrixHOL, HOLPosition }
import scala.collection.mutable

// matches for consts and vars, but nothing else
object VarOrConst {
  def unapply( e: FOLExpression ) = e match {
    case FOLVar( name )   => Some( name )
    case FOLConst( name ) => Some( name )
    case _                => None
  }
}

// Instantiates a term in a quantified formula (using the first quantifier).
object instantiate {
  def apply( f: FOLFormula, t: FOLTerm ): FOLFormula = f match {
    case All( v, form ) =>
      val sub = FOLSubstitution( v, t )
      sub( form )
    case Ex( v, form ) =>
      val sub = FOLSubstitution( v, t )
      sub( form )
    case _ => throw new Exception( "ERROR: trying to replace variables in a formula without quantifier." )
  }
}

/** Returns whether t is a function. */
/** Returns whether t is a function whose name fulfills to a given condition. */
object isFunc {
  def apply( t: FOLTerm ): Boolean = isFunc( t, _ => true )
  def apply( t: FOLTerm, cond: String => Boolean ): Boolean = t match {
    case FOLFunction( f, _ ) => cond( f.toString )
    case _                   => false
  }
}

/** Returns whether t is a variable. */
object isVar {
  def apply( t: FOLTerm ): Boolean = t match {
    case FOLVar( _ ) => true
    case _           => false
  }
}

/** Unsafely extracts the function name from a term. Fails if the term is not a function. */
object fromFunc {
  def apply( t: FOLTerm ) = t match { case FOLFunction( f, _ ) => f }
}

/** Unsafely extracts the function arguments from a term. Fails if the term is not a function. */
object fromFuncArgs {
  def apply( t: FOLTerm ) = t match { case FOLFunction( _, a ) => a }
}

// Instantiates all quantifiers of the formula with the terms in lst.
// OBS: the number of quantifiers in the formula must be greater or equal than the
// number of terms in lst.
object instantiateAll {
  def apply( f: FOLFormula, lst: Seq[FOLTerm] ): FOLFormula = lst match {
    case Nil    => f
    case h :: t => instantiateAll( instantiate( f, h ), t )
  }

  /**
   * If f is a formula \forall x_1 ... x_n G, and lst is a list of lists of terms
   *   such that each list has length <= n, this function returns the list
   *   of instances of f obtained by calling instantiateAll on each list of terms.
   */
  def apply( f: FOLFormula, lst: Seq[Seq[FOLTerm]] )( implicit d: DummyImplicit ): Seq[FOLFormula] =
    lst.map( terms => instantiateAll( f, terms ) )
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

object numOfAtoms {
  def apply( f: FOLFormula ): Int = f match {
    case FOLAtom( _, _ )     => 1
    case FOLFunction( _, _ ) => 1
    case Top() | Bottom()    => 0
    case Imp( f1, f2 )       => numOfAtoms( f1 ) + numOfAtoms( f2 )
    case And( f1, f2 )       => numOfAtoms( f1 ) + numOfAtoms( f2 )
    case Or( f1, f2 )        => numOfAtoms( f1 ) + numOfAtoms( f2 )
    case Ex( x, f )          => numOfAtoms( f )
    case All( x, f )         => numOfAtoms( f )
    case Neg( f )            => numOfAtoms( f )
    case _                   => throw new Exception( "ERROR: Unexpected case while counting the number of atoms." )
  }
}

object replaceFreeOccurenceOf {
  def apply( variable: String, by: String, formula: FOLFormula ): FOLFormula = {
    replaceFreeOccurenceOf( FOLVar( variable ), FOLVar( by ), formula )
  }

  /**
   * Replaces all free ocurrences of a variable by another variable in a FOLTerm.
   *
   * @param variable The name of the free variable to replace.
   * @param by The name of the new variable.
   * @param term The term in which to replace [variable] with [by].
   */
  def apply( variable: String, by: String, term: FOLTerm ): FOLTerm = term match {
    case FOLFunction( f, terms ) => FOLFunction( f, terms.map( x => replaceFreeOccurenceOf( variable, by, x ) ) )
    case ( v @ FOLVar( x ) )     => if ( x.toString() == variable ) FOLVar( by ) else v
    case ( c @ FOLConst( _ ) )   => c
  }

  /**
   * Replaces all free ocurrences of a variable by another variable in a FOL formula.
   *
   * @param variable The name of the free variable to replace.
   * @param by The name of the new variable.
   * @param formula The formula in which to replace [variable] with [by].
   */
  def apply( variable: FOLVar, by: FOLVar, formula: FOLFormula ): FOLFormula = {
    formula match {
      case FOLAtom( _, args ) => FOLSubstitution( variable, by ).apply( formula )

      case Neg( f ) =>
        Neg( replaceFreeOccurenceOf( variable, by, f ) )

      case And( f1, f2 ) =>
        val r1 = replaceFreeOccurenceOf( variable, by, f1 )
        val r2 = replaceFreeOccurenceOf( variable, by, f2 )
        And( r1, r2 )

      case Or( f1, f2 ) =>
        val r1 = replaceFreeOccurenceOf( variable, by, f1 )
        val r2 = replaceFreeOccurenceOf( variable, by, f2 )
        Or( r1, r2 )

      case Ex( v, f ) =>
        if ( v.syntaxEquals( variable ) )
          formula
        else
          Ex( v, replaceFreeOccurenceOf( variable, by, f ) )

      case All( v, f ) =>
        if ( v.syntaxEquals( variable ) )
          formula
        else
          All( v, replaceFreeOccurenceOf( variable, by, f ) )

      case Top() | Bottom() => formula

      case _                => throw new Exception( "Unknown operator encountered during renaming of outermost bound variable. Formula is: " + formula )
    }
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

object addQuantifiers {
  /**
   * Adds a list of universal quantifiers to a FOL formula.
   * The first element of the list will be the outermost quantifier.
   * A generalization of applying All(x,f).
   *
   * It always holds that addQuantifiers(f,removeQuantifiers(f)._1) = f.
   *
   * @param f A FOL formula, typically with the free variables of xs.
   * @param xs A list of variables [x1,...,xn] over which to universally quantify f.
   * @return [forall x1,...,xn] f
   */
  def apply( f: FOLFormula, xs: List[FOLVar] ) = xs.reverse.foldLeft( f )( ( f, x ) => All( x, f ) )
}

object removeQuantifiers {

  /**
   * Strips the initial universal quantifiers from a FOL formula that begins
   * with a quantifier block.
   * A generalization of unapplying All(x,f).
   *
   * @param f A FOL formula of the form [forall x1,...,xn] f'.
   * @return The tuple ([xn,...,x1], f').
   */
  def apply( f: FOLFormula ): ( List[FOLVar], FOLFormula ) = f match {
    case All( x, f ) => {
      val ( xs, fret ) = removeQuantifiers( f )
      ( x :: xs, fret )
    }
    case f => ( List[FOLVar](), f )
  }
}

object univclosure {
  /**
   * Closes the given formula universally
   * @param f the formula to be closed
   * @return forall x_1 ... forall x_n f, where {x_i | 1 <= i <= n} = FV(f)
   */
  def apply( f: FOLFormula ) = freeVariables( f ).foldRight( f )( ( v, g ) => All( v, g ) )
}

object existsclosure {
  /**
   * Closes the given formula existentially
   * @param f the formula to be closed
   * @return exists x_1 ... exists x_n f, where {x_i | 1 <= i <= n} = FV(f)
   */
  def apply( f: FOLFormula ) = freeVariables( f ).foldRight( f )( ( v, g ) => Ex( v, g ) )
}

object removeNQuantifiers {
  /**
   * Removes at most n universal quantifiers from a FOL formula that begins
   * with a quantifier block.
   *
   * See removeQuantifiers.
   *
   * @param f A FOL formula of the form [forall x1,...,xm] f'.
   * @param n The number of quantifiers to strip.
   * @return The tuple ([x1',...,xn], f'') where n' <= n & n' <= m and f' is a subformula
   * of f''.
   */
  def apply( f: FOLFormula, n: Int ): ( List[FOLVar], FOLFormula ) = f match {
    case All( x, f ) => {
      if ( n > 0 ) {
        val ( xs, fret ) = removeNQuantifiers( f, n - 1 )
        ( xs :+ x, fret )
      } else { ( List[FOLVar](), All( x, f ) ) }
    }
    case f => ( List[FOLVar](), f )
  }
}

/**
 * Given varName and an integer n,
 * returns the list [varName_0,...,varName_(n-1)],
 * where varName_i is a FOLVar with the same name.
 */
object createFOLVars {
  def apply( varName: String, n: Int ) = {
    ( 0 to ( n - 1 ) ).map( n => FOLVar( ( varName + "_" + n ) ) ).toList
  }
}

object collectVariables {
  /**
   * Returns the list (not set!) of all occurring variables, free or bound, in a FOL FORMULA, from left to right.
   *
   * @param f The FOL formula in which to collect the variables.
   * @return The list of occurring variables, from left to right. If a variable occurs multiple times
   *         in the formula, it will occur multiple times in the returned list.
   */
  def apply( f: FOLFormula ): List[FOLVar] = f match {
    case And( f1, f2 )    => collectVariables( f1 ) ++ collectVariables( f2 )
    case Or( f1, f2 )     => collectVariables( f1 ) ++ collectVariables( f2 )
    case Imp( f1, f2 )    => collectVariables( f1 ) ++ collectVariables( f2 )
    case Neg( f1 )        => collectVariables( f1 )
    case All( _, f1 )     => collectVariables( f1 )
    case Ex( _, f1 )      => collectVariables( f1 )
    case FOLAtom( _, f1 ) => f1.map( f => collectVariables( f ) ).foldLeft( List[FOLVar]() )( _ ++ _ )
    case Top() | Bottom() => List()
    case _                => throw new IllegalArgumentException( "Unhandled case in fol.utils.collectVariables(FOLFormula)!" )
  }

  /**
   * Returns the list (not set!) of all occurring variables, free or bound, in a FOLTerm, from left to right.
   *
   * @param f The FOLTerm in which to collect the variables.
   * @return The list of occurring variables, from left to right. If a variable occurs multiple times
   *         in the formula, it will occur multiple times in the returned list.
   */
  def apply( f: FOLTerm ): List[FOLVar] = f match {
    case FOLVar( x )             => List( FOLVar( x ) )
    case FOLFunction( _, terms ) => terms.map( t => collectVariables( t ) ).foldLeft( List[FOLVar]() )( _ ++ _ )
    case FOLConst( _ )           => Nil
    case _                       => throw new IllegalArgumentException( "Unhandled case in fol.utils.collectVariables(FOLTerm)!" )
  }
}

object isEigenvariable {
  def apply( x: FOLVar, eigenvariable: String ) = x.toString.split( '_' ) match {
    case Array( eigenvariable, n ) => n.forall( Character.isDigit )
    case _                         => false
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

  // TODO: these functions should go to listSupport in dssupport in the
  // utils project.

  def removeDoubles[T]( l: List[T] ): List[T] = {
    removeDoubles_( l.reverse ).reverse
  }

  private def removeDoubles_[T]( l: List[T] ): List[T] = {
    l match {
      case head :: tail =>
        if ( tail.contains( head ) )
          removeDoubles( tail )
        else
          head :: removeDoubles( tail )
      case Nil => Nil
    }
  }

  //auxiliary function which removes duplications from list of type:
  //List[List[(String, Tree[AnyRef], Set[FormulaOccurrence])]]
  //and type
  ////List[List[(String, Tree[AnyRef], (Set[FormulaOccurrence], Set[FormulaOccurrence]))]]

  def removeDoubles3[T, R]( l: List[Tuple3[String, T, R]] ): List[Tuple3[String, T, R]] = {
    l match {
      case head :: tail =>
        if ( tail.map( tri => tri._3 ).contains( head._3 ) )
          removeDoubles3( tail )
        else
          head :: removeDoubles3( tail )
      case Nil => Nil
    }
  }

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
   * by replacing the code construction for logic symbols by string versions in the file language/hol/logicSymbols.scala.
   * Several recursive function calls will be transformed into an abbreviated form (e.g. f(f(f(x))) => f^3^(x)).
   * Terms are also handled by the this function.
   *
   * @param  e  The method has no parameters other then the object which is to be written as a string
   *
   * @throws Exception This occurs when an unknown subformula is found when parsing the FOL construction
   *
   * @return A String which contains the defined symbols in language/hol/logicSymbols.scala.
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
