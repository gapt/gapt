/*
 * Replacements.scala
 *
 */

package at.logic.gapt.language.hol
import at.logic.gapt.expr._

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
case class Replacement( position: List[Int], expression: LambdaExpression ) {
  /**
   * Applies the replacement of the classes expression at the classes position to the given term.
   * @param term The term in which we perform the replacement.
   * @return an expression identical to term except that it contains expression as a subtree at the position
   */
  def apply( term: LambdaExpression ): LambdaExpression = replace( position, term )

  // To avoid all the casting...
  private def replace( pos: List[Int], f: HOLFormula ): HOLFormula =
    replace( pos, f.asInstanceOf[LambdaExpression] ).asInstanceOf[HOLFormula]

  private def replace( pos: List[Int], exp: LambdaExpression ): LambdaExpression = {
    ( pos, exp ) match {
      case ( 1 :: rest, And( m, n ) ) => And( replace( rest, m ), n )
      case ( 2 :: rest, And( m, n ) ) => And( m, replace( rest, n ) )
      case ( 1 :: rest, Or( m, n ) )  => Or( replace( rest, m ), n )
      case ( 2 :: rest, Or( m, n ) )  => Or( m, replace( rest, n ) )
      case ( 1 :: rest, Imp( m, n ) ) => Imp( replace( rest, m ), n )
      case ( 2 :: rest, Imp( m, n ) ) => Imp( m, replace( rest, n ) )
      case ( 1 :: rest, Neg( m ) )    => Neg( replace( rest, m ) )
      case ( 1 :: rest, Ex( v, m ) )  => Ex( v, replace( rest, m ) )
      case ( 1 :: rest, All( v, m ) ) => All( v, replace( rest, m ) )
      case ( 1 :: rest, Eq( m, n ) )  => Eq( replace( rest, m ), n )
      case ( 2 :: rest, Eq( m, n ) )  => Eq( m, replace( rest, n ) )
      case ( n :: rest, HOLAtom( p: Const, args ) ) => {
        val ( firstArgs, arg :: remainingArgs ) = args.splitAt( n - 1 )
        HOLAtom( p, firstArgs ::: ( replace( rest, arg ) :: remainingArgs ) )
      }
      case ( n :: rest, HOLAtom( p: Var, args ) ) => {
        val ( firstArgs, arg :: remainingArgs ) = args.splitAt( n - 1 )
        HOLAtom( p, firstArgs ::: ( replace( rest, arg ) :: remainingArgs ) )
      }
      case ( n :: rest, HOLFunction( p: Const, args ) ) => {
        val ( firstArgs, arg :: remainingArgs ) = args.splitAt( n - 1 )
        HOLFunction( p, firstArgs ::: ( replace( rest, arg ) :: remainingArgs ) )
      }
      case ( n :: rest, HOLFunction( p: Var, args ) ) => {
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
@deprecated
object getAllPositions {
  /**
   * Calculates a list of all subterms of an expression together with their respective positions.
   * @param expression an arbitrary hol epxression
   * @return a list of pairs (position, subterm)
   */
  def apply( expression: LambdaExpression ): List[Tuple2[List[Int], LambdaExpression]] = getAllPositions2( expression ) filter ( _ match {
    case Var( _, _ ) => false
    case _           => true
  } )
}

//TODO: Refactor this workaround, which is used for the trat grammar decomposition (Used in getAllPositionsFOL). It just handles the Var differently than getAllPositions
/**
 * Calculates a list of all subterms of an expression together with their respective positions.
 */
@deprecated
object getAllPositions2 {
  /**
   * Calculates a list of all subterms of an expression together with their respective positions.
   * @param expression an arbitrary hol epxression
   * @return a list of pairs (position, subterm)
   */
  def apply( expression: LambdaExpression ): List[Tuple2[List[Int], LambdaExpression]] = recApply( expression, List() )
  private def recApply( t: LambdaExpression, curPos: List[Int] ): List[( List[Int], LambdaExpression )] = t match {
    case Var( _, _ )   => ( curPos, t ) :: Nil
    case Const( _, _ ) => ( curPos, t ) :: Nil
    case Ex( _, exp )  => ( curPos, t ) :: recApply( exp, curPos ::: List( 1 ) )
    case All( _, exp ) => ( curPos, t ) :: recApply( exp, curPos ::: List( 1 ) )
    case HOLAtom( _, args ) => ( curPos, t ) :: args.zipWithIndex.flatMap( el =>
      recApply( el._1.asInstanceOf[LambdaExpression], curPos ::: List( el._2 + 1 ) ) )
    case HOLFunction( _, args ) => ( curPos, t ) :: args.zipWithIndex.flatMap( el =>
      recApply( el._1.asInstanceOf[LambdaExpression], curPos ::: List( el._2 + 1 ) ) )
    case Abs( _, exp ) => ( curPos, t ) :: recApply( exp, curPos ::: List( 1 ) )
    case Neg( f )      => ( curPos, t ) :: recApply( f, curPos ::: List( 1 ) )
    case Or( f, g )    => ( curPos, t ) :: recApply( f, curPos ::: List( 1 ) ) ::: recApply( g, curPos ::: List( 2 ) )
    case And( f, g )   => ( curPos, t ) :: recApply( f, curPos ::: List( 1 ) ) ::: recApply( g, curPos ::: List( 2 ) )
    case Imp( f, g )   => ( curPos, t ) :: recApply( f, curPos ::: List( 1 ) ) ::: recApply( g, curPos ::: List( 2 ) )
    case App( s, t ) =>
      throw new Exception( "Application of " + s + " to " + t + " is unhandled (no logical operator, no Atom, no Function)!" )
    case _ =>
      throw new Exception( "Case for " + t + " not handled!" )
  }
}

/**
 * Returns a specific subterm within a position.
 */
@deprecated
object getAtPosition {
  /**
   * Returns the subterm at expression | pos
   * @param expression An arbitrary hol expression
   * @param pos A path of branchings in the term tree. Nil is the root position, 1 is the first argument  etc.
   * @return The subterm, if it exists.
   */
  def apply( expression: LambdaExpression, pos: List[Int] ): LambdaExpression = ( expression, pos ) match {
    case ( t, Nil )                            => t
    case ( Var( _, _ ), n )                    => throw new IllegalArgumentException( "trying to obtain a subterm of a variable at position: " + n )
    case ( Const( _, _ ), n )                  => throw new IllegalArgumentException( "trying to obtain a subterm of a constant at position: " + n )
    case ( All( _, exp ), 1 :: rest )          => getAtPosition( exp, rest )
    case ( Ex( _, exp ), 1 :: rest )           => getAtPosition( exp, rest )
    case ( HOLAtom( _, args ), n :: rest )     => getAtPosition( args( n - 1 ).asInstanceOf[LambdaExpression], rest )
    case ( HOLFunction( _, args ), n :: rest ) => getAtPosition( args( n - 1 ).asInstanceOf[LambdaExpression], rest )
    case ( Abs( _, exp ), 1 :: rest )          => getAtPosition( exp, rest )
    case ( _, n :: rest )                      => throw new IllegalArgumentException( "trying to obtain a subterm of " + expression + " at position: " + n )
  }
}

/*object ImplicitConverters {
  implicit def convertPairToReplacement(pair: Tuple2[List[Int],LambdaExpression]):Replacement = Replacement(pair._1, pair._2)
  implicit def convertReplacementToPair(rep: Replacement):Tuple2[List[Int],LambdaExpression] = (rep.position, rep.expression)
}*/
