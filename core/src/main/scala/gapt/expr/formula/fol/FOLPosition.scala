package gapt.expr.formula.fol

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Eq
import gapt.expr.formula.Ex
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.hol.HOLPosition
import gapt.expr.util
import gapt.expr.util.LambdaPosition

object FOLPosition {
  def apply( is: Int* ) = new FOLPosition( is.toList )

  def toList( pos: FOLPosition ): List[Int] = pos.list

  /**
   * Returns a list of positions of subexpressions that satisfy some predicate.
   *
   * This function is a wrapper around [[gapt.expr.formula.hol.HOLPosition.getPositions]].
   *
   * @param exp The expression under consideration.
   * @param pred The predicate to be evaluated. Defaults to "always true", i.e. if called without this argument, the function will return all positions.
   * @return Positions of subexpressions satisfying pred.
   */
  def getPositions( exp: FOLExpression, pred: FOLExpression => Boolean = _ => true ): List[FOLPosition] = {
    HOLPosition.getPositions( exp, {
      case e: FOLExpression => pred( e )
      case _                => false
    } ) filter {
      definesFOLPosition( exp )
    } map {
      toFOLPosition( exp )
    }
  }

  /**
   * Replaces a a subexpression in a FOLFormula. This function is actually a wrapper around [[gapt.expr.util.LambdaPosition.replace]].
   *
   * @param f The formula in which to perform the replacement.
   * @param pos The position at which to replace.
   * @param repTerm The expression that f(pos) should be replaced with.
   * @return
   */
  def replace( f: FOLFormula, pos: FOLPosition, repTerm: FOLExpression ): FOLFormula = replace( f.asInstanceOf[FOLExpression], pos, repTerm ).asInstanceOf[FOLFormula]

  /**
   * Replaces a a subexpression in a FOLExpression. This function is actually a wrapper around [[gapt.expr.util.LambdaPosition.replace]].
   *
   * @param f The expression in which to perform the replacement.
   * @param pos The position at which to replace.
   * @param repTerm The expression that f(pos) should be replaced with.
   * @return
   */
  def replace( f: FOLExpression, pos: FOLPosition, repTerm: FOLExpression ): FOLExpression = {
    val holPos = toHOLPosition( f )( pos )
    HOLPosition.replace( f, holPos, repTerm ).asInstanceOf[FOLFormula]
  }

  /**
   * Compares two FOLExpressions and returns the list of outermost positions where they differ.
   *
   * @param exp1 The first expression.
   * @param exp2 The second expression.
   * @return The list of outermost positions at which exp1 and exp2 differ.
   */
  def differingPositions( exp1: FOLExpression, exp2: FOLExpression ): List[FOLPosition] = HOLPosition.differingPositions( exp1, exp2 ) map { toFOLPosition( exp1 ) }

  def definesFOLPosition( exp: FOLExpression )( pos: HOLPosition ): Boolean = {
    if ( pos.isEmpty )
      true
    else {
      val rest = pos.tail
      exp match {
        case FOLFunction( _, args ) =>
          if ( !( pos.toList contains 2 ) )
            false
          else {
            val n = args.length
            val ( left, right ) = mySplit( pos.toList )
            val k = left.length
            k <= n && definesFOLPosition( args( n - k ) )( HOLPosition( right ) )
          }
        case FOLAtom( _, args ) =>
          if ( !( pos.toList contains 2 ) )
            false
          else {
            val n = args.length
            val ( left, right ) = mySplit( pos.toList )
            val k = left.length
            k <= n && definesFOLPosition( args( n - k ) )( HOLPosition( right ) )
          }

        case Neg( f ) =>
          pos.head == 1 && definesFOLPosition( f )( rest )

        case BinaryConnective( l, r ) =>
          ( pos.head == 1 && definesFOLPosition( l )( rest ) ) ||
            ( pos.head == 2 && definesFOLPosition( r )( rest ) )

        case All( x, f ) =>
          pos.head == 1 && definesFOLPosition( f )( rest )

        case Ex( x, f ) =>
          pos.head == 1 && definesFOLPosition( f )( rest )
      }
    }
  }

  def toFOLPosition( exp: FOLExpression )( pos: HOLPosition ): FOLPosition = {
    if ( pos.isEmpty )
      FOLPosition()
    else {
      exp match {
        case FOLFunction( _, args ) =>
          if ( !( pos.toList contains 2 ) )
            throw new Exception( "Can't convert position " + pos + " for expression " + exp + " to FOLPosition." )
          val n = args.length
          val ( left, right ) = mySplit( pos.toList )
          val k = left.length
          if ( k <= n )
            ( n - k + 1 ) :: toFOLPosition( args( n - k ) )( HOLPosition( right ) )
          else throw new Exception( "Can't convert position " + pos + " for expression " + exp + " to FOLPosition." )

        case FOLAtom( _, args ) =>
          if ( !( pos.toList contains 2 ) )
            throw new Exception( "Can't convert position " + pos + " for expression " + exp + " to FOLPosition." )
          val n = args.length
          val ( left, right ) = mySplit( pos.toList )
          val k = left.length
          if ( k <= n )
            ( n - k + 1 ) :: toFOLPosition( args( n - k ) )( HOLPosition( right ) )
          else throw new Exception( "Can't convert position " + pos + " for expression " + exp + " to FOLPosition." )

        case Neg( f ) if pos.head == 1 =>
          1 :: toFOLPosition( f )( pos.tail )

        case BinaryConnective( l, _ ) if pos.head == 1 =>
          1 :: toFOLPosition( l )( pos.tail )
        case BinaryConnective( _, r ) if pos.head == 2 =>
          2 :: toFOLPosition( r )( pos.tail )

        case All( x, f ) if pos.head == 1 =>
          1 :: toFOLPosition( f )( pos.tail )

        case Ex( x, f ) if pos.head == 1 =>
          1 :: toFOLPosition( f )( pos.tail )

        case _ => throw new Exception( "Can't convert position " + pos + " for expression " + exp + " to FOLPosition." )
      }
    }
  }

  def toHOLPosition( exp: FOLExpression )( pos: FOLPosition ): HOLPosition = {
    if ( pos.isEmpty )
      HOLPosition()
    else exp match {
      case FOLFunction( _, args ) =>
        val k = pos.head
        val subPos = toHOLPosition( args( k - 1 ) )( pos.tail )
        List.fill( args.length - k )( 1 ).foldRight( 2 :: subPos )( ( i, acc ) => i :: acc )

      case FOLAtom( _, args ) =>
        val k = pos.head
        val subPos = toHOLPosition( args( k - 1 ) )( pos.tail )
        List.fill( args.length - k )( 1 ).foldRight( 2 :: subPos )( ( i, acc ) => i :: acc )

      case Neg( f ) if pos.head == 1 =>
        1 :: toHOLPosition( f )( pos.tail )

      case BinaryConnective( l, _ ) if pos.head == 1 =>
        1 :: toHOLPosition( l )( pos.tail )

      case BinaryConnective( _, r ) if pos.head == 2 =>
        2 :: toHOLPosition( r )( pos.tail )

      case All( x, f ) if pos.head == 1 =>
        1 :: toHOLPosition( f )( pos.tail )

      case Ex( x, f ) if pos.head == 1 =>
        1 :: toHOLPosition( f )( pos.tail )

      case _ => throw new Exception( "Can't convert position " + pos + " for expression " + exp + " to FOLPosition." )
    }
  }

  def toHOLPositionOption( exp: FOLExpression )( pos: FOLPosition ): Option[HOLPosition] = {
    if ( pos.isEmpty )
      Some( HOLPosition() )
    else exp match {
      case FOLFunction( _, args ) =>
        val k = pos.head
        val subPos = toHOLPosition( args( k - 1 ) )( pos.tail )
        Some( List.fill( args.length - k )( 1 ).foldRight( 2 :: subPos )( ( i, acc ) => i :: acc ) )

      case FOLAtom( _, args ) =>
        val k = pos.head
        val subPos = toHOLPosition( args( k - 1 ) )( pos.tail )
        Some( List.fill( args.length - k )( 1 ).foldRight( 2 :: subPos )( ( i, acc ) => i :: acc ) )

      case Neg( f ) if pos.head == 1 =>
        Some( 1 :: toHOLPosition( f )( pos.tail ) )

      case BinaryConnective( l, _ ) if pos.head == 1 =>
        Some( 1 :: toHOLPosition( l )( pos.tail ) )

      case BinaryConnective( _, r ) if pos.head == 2 =>
        Some( 2 :: toHOLPosition( r )( pos.tail ) )

      case All( x, f ) if pos.head == 1 =>
        Some( 1 :: toHOLPosition( f )( pos.tail ) )

      case Ex( x, f ) if pos.head == 1 =>
        Some( 1 :: toHOLPosition( f )( pos.tail ) )

      case _ => None
    }
  }

  private def mySplit( left: List[Int], right: List[Int] ): ( List[Int], List[Int] ) =
    if ( right.isEmpty )
      ( left, right )
    else right.head match {
      case 1 => mySplit( left :+ 1, right.tail )
      case 2 => ( left :+ 2, right.tail )
    }

  private def mySplit( list: List[Int] ): ( List[Int], List[Int] ) = mySplit( Nil, list )
}

/**
 * Positions are given as lists of Integers. The empty list denotes the current expression itself.
 * A list starting with k denotes a subexpression in the k^th^ argument of the current expression.
 * @param list The list describing the position.
 */
case class FOLPosition( list: List[Int] ) {
  require( list.forall( _ > 0 ) )

  def toList: List[Int] = list
  def head: Int = list.head
  def headOption: Option[Int] = list.headOption
  def tail = FOLPosition( list.tail )
  def isEmpty: Boolean = list.isEmpty
  override def toString = s"[${list.mkString( "," )}]"

  def ::( x: Int ): FOLPosition = FOLPosition( x :: list )
}

object BinaryConnective {
  def unapply( exp: FOLExpression ): Option[( FOLExpression, FOLExpression )] = exp match {
    case And( l, r ) => Some( l, r )
    case Or( l, r )  => Some( l, r )
    case Imp( l, r ) => Some( l, r )
    case Eq( l, r )  => Some( l, r )
    case _           => None
  }
}