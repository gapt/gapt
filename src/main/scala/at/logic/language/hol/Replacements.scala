/*
 * Replacements.scala
 *
 */

package at.logic.language.hol

/**
 * Replacement represents the rewriting notion of a hole at a certain position. We expect that
 * the passed expression will replace the subterm indicated at the given position. Positions are
 * denoted like in term rewriting.
 * @example {{{
 *          val expr = And(Atom("P", List(FOLConst("a"), FOLConst("b"))), Atom("Q", Nil))
 *          val f = Replacement(List(1,2), FOLVar("x" ))(expr)
 *          f == And(Atom("P", List(FOLConst("a"), FOLVar("x"))), Atom("Q", Nil))
 *          }}}
 *
 * @param position A path of branchings in the term tree. Nil is the root position, 1 is the first argument  etc.
 * @param expression The term which will be inserted.
 */
case class Replacement( position: List[Int], expression: HOLExpression ) {
  /**
   * Applies the replacement of the classes expression at the classes position to the given term.
   * @param term The term in which we perform the replacement.
   * @return an expression identical to term except that it contains expression as a subtree at the position
   */
  def apply( term: HOLExpression ): HOLExpression = replace( position, term )

  // To avoid all the casting...
  private def replace( pos: List[Int], f: HOLFormula ): HOLFormula =
    replace( pos, f.asInstanceOf[HOLExpression] ).asInstanceOf[HOLFormula]

  private def replace( pos: List[Int], exp: HOLExpression ): HOLExpression = {
    ( pos, exp ) match {
      case ( 1 :: rest, HOLAnd( m, n ) )      => HOLAnd( replace( rest, m ), n )
      case ( 2 :: rest, HOLAnd( m, n ) )      => HOLAnd( m, replace( rest, n ) )
      case ( 1 :: rest, HOLOr( m, n ) )       => HOLOr( replace( rest, m ), n )
      case ( 2 :: rest, HOLOr( m, n ) )       => HOLOr( m, replace( rest, n ) )
      case ( 1 :: rest, HOLImp( m, n ) )      => HOLImp( replace( rest, m ), n )
      case ( 2 :: rest, HOLImp( m, n ) )      => HOLImp( m, replace( rest, n ) )
      case ( 1 :: rest, HOLNeg( m ) )         => HOLNeg( replace( rest, m ) )
      case ( 1 :: rest, HOLExVar( v, m ) )    => HOLExVar( v, replace( rest, m ) )
      case ( 1 :: rest, HOLAllVar( v, m ) )   => HOLAllVar( v, replace( rest, m ) )
      case ( 1 :: rest, HOLEquation( m, n ) ) => HOLEquation( replace( rest, m ), n )
      case ( 2 :: rest, HOLEquation( m, n ) ) => HOLEquation( m, replace( rest, n ) )
      case ( n :: rest, HOLAtom( p: HOLConst, args ) ) => {
        val ( firstArgs, arg :: remainingArgs ) = args.splitAt( n - 1 )
        HOLAtom( p, firstArgs ::: ( replace( rest, arg ) :: remainingArgs ) )
      }
      case ( n :: rest, HOLAtom( p: HOLVar, args ) ) => {
        val ( firstArgs, arg :: remainingArgs ) = args.splitAt( n - 1 )
        HOLAtom( p, firstArgs ::: ( replace( rest, arg ) :: remainingArgs ) )
      }
      case ( n :: rest, HOLFunction( p: HOLConst, args, t ) ) => {
        val ( firstArgs, arg :: remainingArgs ) = args.splitAt( n - 1 )
        HOLFunction( p, firstArgs ::: ( replace( rest, arg ) :: remainingArgs ) )
      }
      case ( n :: rest, HOLFunction( p: HOLVar, args, t ) ) => {
        val ( firstArgs, arg :: remainingArgs ) = args.splitAt( n - 1 )
        HOLFunction( p, firstArgs ::: ( replace( rest, arg ) :: remainingArgs ) )
      }
      case ( Nil, _ ) => expression
      case _          => throw new IllegalArgumentException( "Position (" + pos + ") does not exist in the expression (" + exp + ")" )
    }
  }
}

/**
 * Calculates a list of all subterms of an expression together with their respective positions.
 * Variabls are excluded. To include them, use getAllPositions2.
 */
//TODO: rename getAllpositions2 to getAllPositions and replace calls to this by the general method and filter
object getAllPositions {
  /**
   * Calculates a list of all subterms of an expression together with their respective positions.
   * @param expression an arbitrary hol epxression
   * @return a list of pairs (position, subterm)
   */
  def apply( expression: HOLExpression ): List[Tuple2[List[Int], HOLExpression]] = getAllPositions2( expression ) filter ( _ match {
    case HOLVar( _, _ ) => false
    case _              => true
  } )
}

//TODO: Refactor this workaround, which is used for the trat grammar decomposition (Used in getAllPositionsFOL). It just handles the HOLVar differently than getAllPositions
/**
 * Calculates a list of all subterms of an expression together with their respective positions.
 */
object getAllPositions2 {
  /**
   * Calculates a list of all subterms of an expression together with their respective positions.
   * @param expression an arbitrary hol epxression
   * @return a list of pairs (position, subterm)
   */
  def apply( expression: HOLExpression ): List[Tuple2[List[Int], HOLExpression]] = recApply( expression, List() )
  private def recApply( t: HOLExpression, curPos: List[Int] ): List[( List[Int], HOLExpression )] = t match {
    case HOLVar( _, _ )      => ( curPos, t ) :: Nil
    case HOLConst( _, _ )    => ( curPos, t ) :: Nil
    case HOLExVar( _, exp )  => ( curPos, t ) :: recApply( exp, curPos ::: List( 1 ) )
    case HOLAllVar( _, exp ) => ( curPos, t ) :: recApply( exp, curPos ::: List( 1 ) )
    case HOLAtom( _, args ) => ( curPos, t ) :: args.zipWithIndex.flatMap( el =>
      recApply( el._1.asInstanceOf[HOLExpression], curPos ::: List( el._2 + 1 ) ) )
    case HOLFunction( _, args, _ ) => ( curPos, t ) :: args.zipWithIndex.flatMap( el =>
      recApply( el._1.asInstanceOf[HOLExpression], curPos ::: List( el._2 + 1 ) ) )
    case HOLAbs( _, exp ) => ( curPos, t ) :: recApply( exp, curPos ::: List( 1 ) )
    case HOLNeg( f )      => ( curPos, t ) :: recApply( f, curPos ::: List( 1 ) )
    case HOLOr( f, g )    => ( curPos, t ) :: recApply( f, curPos ::: List( 1 ) ) ::: recApply( g, curPos ::: List( 2 ) )
    case HOLAnd( f, g )   => ( curPos, t ) :: recApply( f, curPos ::: List( 1 ) ) ::: recApply( g, curPos ::: List( 2 ) )
    case HOLImp( f, g )   => ( curPos, t ) :: recApply( f, curPos ::: List( 1 ) ) ::: recApply( g, curPos ::: List( 2 ) )
    case HOLApp( s, t ) =>
      throw new Exception( "Application of " + s + " to " + t + " is unhandled (no logical operator, no Atom, no Function)!" )
    case _ =>
      throw new Exception( "Case for " + t + " not handled!" )
  }
}

/**
 * Returns a specific subterm within a position.
 */
object getAtPosition {
  /**
   * Returns the subterm at expression | pos
   * @param expression An arbitrary hol expression
   * @param pos A path of branchings in the term tree. Nil is the root position, 1 is the first argument  etc.
   * @return The subterm, if it exists.
   */
  def apply( expression: HOLExpression, pos: List[Int] ): HOLExpression = ( expression, pos ) match {
    case ( t, Nil )                               => t
    case ( HOLVar( _, _ ), n )                    => throw new IllegalArgumentException( "trying to obtain a subterm of a variable at position: " + n )
    case ( HOLConst( _, _ ), n )                  => throw new IllegalArgumentException( "trying to obtain a subterm of a constant at position: " + n )
    case ( HOLAllVar( _, exp ), 1 :: rest )       => getAtPosition( exp, rest )
    case ( HOLExVar( _, exp ), 1 :: rest )        => getAtPosition( exp, rest )
    case ( HOLAtom( _, args ), n :: rest )        => getAtPosition( args( n - 1 ).asInstanceOf[HOLExpression], rest )
    case ( HOLFunction( _, args, _ ), n :: rest ) => getAtPosition( args( n - 1 ).asInstanceOf[HOLExpression], rest )
    case ( HOLAbs( _, exp ), 1 :: rest )          => getAtPosition( exp, rest )
    case ( _, n :: rest )                         => throw new IllegalArgumentException( "trying to obtain a subterm of " + expression + " at position: " + n )
  }
}

/*object ImplicitConverters {
  implicit def convertPairToReplacement(pair: Tuple2[List[Int],HOLExpression]):Replacement = Replacement(pair._1, pair._2)
  implicit def convertReplacementToPair(rep: Replacement):Tuple2[List[Int],HOLExpression] = (rep.position, rep.expression)
}*/
