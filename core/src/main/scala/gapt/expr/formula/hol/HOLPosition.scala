package gapt.expr.formula.hol

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.util
import gapt.expr.util
import gapt.expr.util.LambdaPosition

object HOLPosition {
  def apply( is: Int* ) = new HOLPosition( is.toList )

  def toList( pos: HOLPosition ): List[Int] = pos.list

  /**
   * Returns a list of positions of subexpressions that satisfy some predicate.
   *
   * This function is a wrapper around [[gapt.expr.util.LambdaPosition.getPositions]].
   *
   * @param exp The expression under consideration.
   * @param pred The predicate to be evaluated. Defaults to "always true", i.e. if called without this argument, the function will return all positions.
   * @return Positions of subexpressions satisfying pred.
   */
  def getPositions( exp: Expr, pred: Expr => Boolean = _ => true ): List[HOLPosition] = {
    LambdaPosition.getPositions( exp, {
      case e: Expr => pred( e )
      case _       => false
    } ) filter { definesHOLPosition( exp ) } map { toHOLPosition( exp ) }
  }

  /**
   * Replaces a a subexpression in a Formula. This function is actually a wrapper around [[util.LambdaPosition.replace]].
   *
   * @param f The formula in which to perform the replacement.
   * @param pos The position at which to replace.
   * @param repTerm The expression that f(pos) should be replaced with.
   * @return
   */
  def replace( f: Formula, pos: HOLPosition, repTerm: Expr ): Formula = replace( f.asInstanceOf[Expr], pos, repTerm ).asInstanceOf[Formula]

  /**
   * Replaces a a subexpression in a Expr. This function is actually a wrapper around [[util.LambdaPosition.replace]].
   *
   * @param exp The expression in which to perform the replacement.
   * @param pos The position at which to replace.
   * @param repTerm The expression that exp(pos) should be replaced with.
   * @return
   */
  def replace( exp: Expr, pos: HOLPosition, repTerm: Expr ): Expr = LambdaPosition.replace( exp, toLambdaPosition( exp )( pos ), repTerm )

  /**
   * Compares to Exprs and returns the list of outermost positions where they differ.
   *
   * @param exp1 The first expression.
   * @param exp2 The second expression.
   * @return The list of outermost positions at which exp1 and exp2 differ.
   */
  def differingPositions( exp1: Expr, exp2: Expr ): List[HOLPosition] = LambdaPosition.differingPositions( exp1, exp2 ) map { toHOLPosition( exp1 ) }

  /**
   * Converts a HOLPosition into the corresponding LambdaPosition.
   *
   * Note that position conversion is always relative to a given expression.
   * @param pos The position to be converted.
   * @param exp The relevant Expr.
   * @return The corresponding LambdaPosition.
   */
  def toLambdaPosition( exp: Expr )( pos: HOLPosition ): LambdaPosition = toLambdaPositionOption( exp )( pos ) match {
    case Some( p ) => p
    case None      => throw new Exception( "Can't convert position " + pos + " for expression " + exp + " to LambdaPosition." )
  }

  /**
   * Converts a HOLPosition into the corresponding LambdaPosition, if one exists.
   *
   * Note that position conversion is always relative to a given expression.
   * @param pos The position to be converted.
   * @param exp The relevant Expr.
   * @return The corresponding LambdaPosition.
   */
  def toLambdaPositionOption( exp: Expr )( pos: HOLPosition ): Option[LambdaPosition] = {
    if ( pos.isEmpty ) Some( LambdaPosition() )
    else {
      val rest = pos.tail
      ( pos.head, exp ) match {
        case ( 1, Neg( subExp ) ) =>
          toLambdaPositionOption( subExp )( rest ) match {
            case Some( subPos ) => Some( 2 :: subPos )
            case None           => None
          }

        case ( _, Neg( _ ) ) => None

        case ( 1, Ex( _, subExp ) ) =>
          toLambdaPositionOption( subExp )( rest ) match {
            case Some( subPos ) => Some( 2 :: 1 :: subPos )
            case None           => None
          }

        case ( _, Ex( _, _ ) ) => None

        case ( 1, All( _, subExp ) ) =>
          toLambdaPositionOption( subExp )( rest ) match {
            case Some( subPos ) => Some( 2 :: 1 :: subPos )
            case None           => None
          }

        case ( 1, BinaryConnective( left, _ ) ) =>
          toLambdaPositionOption( left )( rest ) match {
            case Some( leftPos ) => Some( 1 :: 2 :: leftPos )
            case None            => None
          }

        case ( 2, BinaryConnective( _, right ) ) =>
          toLambdaPositionOption( right )( rest ) match {
            case Some( rightPos ) => Some( 2 :: rightPos )
            case None             => None
          }

        case ( _, BinaryConnective( _, _ ) ) => None

        case ( 1, App( f, _ ) ) => toLambdaPositionOption( f )( rest ) match {
          case Some( subPos ) => Some( 1 :: subPos )
          case None           => None
        }

        case ( 2, App( _, arg ) ) => toLambdaPositionOption( arg )( rest ) match {
          case Some( subPos ) => Some( 2 :: subPos )
          case None           => None
        }

        case ( 1, Abs( _, term ) ) => toLambdaPositionOption( term )( rest ) match {
          case Some( subPos ) => Some( 1 :: subPos )
          case None           => None
        }

        case _ => None
      }
    }
  }

  /**
   * Converts a LambdaPosition into the corresponding HOLPosition.
   *
   * Note that position conversion is always relative to a given expression.
   * @param pos The position to be converted.
   * @param exp The relevant Expr.
   * @return The corresponding HOLPosition.
   */
  def toHOLPosition( exp: Expr )( pos: LambdaPosition ): HOLPosition = {
    if ( pos.isEmpty ) HOLPosition()
    else {
      val rest = pos.tail
      exp match {
        case Neg( subExp ) =>
          if ( pos.head == 2 )
            1 :: toHOLPosition( subExp )( rest )
          else
            throw new Exception( "Can't convert position " + pos + " for expression " + exp + " to HOLPosition." )

        case BinaryConnective( left, right ) =>
          if ( pos.head == 1 && rest.headOption.contains( 2 ) )
            1 :: toHOLPosition( left )( rest.tail )
          else if ( pos.head == 2 )
            2 :: toHOLPosition( right )( rest )
          else throw new Exception( "Can't convert position " + pos + " for expression " + exp + " to HOLPosition." )

        case Ex( _, subExp ) =>
          if ( pos.head == 2 && rest.headOption.contains( 1 ) )
            1 :: toHOLPosition( subExp )( rest.tail )
          else throw new Exception( "Can't convert position " + pos + " for expression " + exp + " to HOLPosition." )

        case All( _, subExp ) =>
          if ( pos.head == 2 && rest.headOption.contains( 1 ) )
            1 :: toHOLPosition( subExp )( rest.tail )
          else throw new Exception( "Can't convert position " + pos + " for expression " + exp + " to HOLPosition." )

        case App( f, arg ) =>
          if ( pos.head == 1 )
            1 :: toHOLPosition( f )( rest )
          else if ( pos.head == 2 )
            2 :: toHOLPosition( arg )( rest )
          else throw new Exception( "Can't convert position " + pos + " for expression " + exp + " to HOLPosition." )

        case Abs( _, term ) =>
          if ( pos.head == 1 )
            1 :: toHOLPosition( term )( rest )
          else throw new Exception( "Can't convert position " + pos + " for expression " + exp + " to HOLPosition." )

        case _ => throw new Exception( "Can't convert position " + pos + " for expression " + exp + " to HOLPosition." )
      }
    }
  }

  /**
   * Tests whether a LambdaPosition denotes a HOLPosition for the given expression.
   *
   * @param exp
   * @param pos
   * @return
   */
  def definesHOLPosition( exp: Expr )( pos: LambdaPosition ): Boolean = {
    if ( pos.isEmpty ) true
    else {
      val rest = pos.tail
      exp match {
        case Neg( subExp ) =>
          if ( pos.head == 2 )
            definesHOLPosition( subExp )( rest )
          else
            false

        case BinaryConnective( left, right ) =>
          if ( pos.head == 1 && rest.headOption.contains( 2 ) )
            definesHOLPosition( left )( rest.tail )
          else if ( pos.head == 2 )
            definesHOLPosition( right )( rest )
          else false

        case Ex( _, subExp ) =>
          if ( pos.head == 2 && rest.headOption.contains( 1 ) )
            definesHOLPosition( subExp )( rest.tail )
          else false

        case All( _, subExp ) =>
          if ( pos.head == 2 && rest.headOption.contains( 1 ) )
            definesHOLPosition( subExp )( rest.tail )
          else false

        case App( f, arg ) =>
          if ( pos.head == 1 )
            definesHOLPosition( f )( rest )
          else if ( pos.head == 2 )
            definesHOLPosition( arg )( rest )
          else false

        case Abs( _, term ) =>
          if ( pos.head == 1 )
            definesHOLPosition( term )( rest )
          else false

        case _ => false
      }
    }
  }
}

/**
 * Represents a position in a [[gapt.expr.Expr]].
 *
 * Positions are represented by lists of Integers. The empty list denotes the expression itself.
 * A nonempty list denotes a position in the left or right subexpression according to whether it starts with 1 or 2.
 *
 * The difference between this and [[gapt.expr.util.LambdaPosition]] lies in the handling of quantifiers and binary logical
 * connectives. LambdaPositions treat e.g. conjunctions like any other function, while HOLPositions treat them naturally,
 * i.e. 1 denotes the left conjunct and 2 the right conjunct.
 *
 * Note that this can cause unexpeted behavior: Say a variable of type o -> o -> o is substituted by ∧ in some expression.
 * The LambdaPositions will stay the same, but the HOLPositions won't.
 *
 * @param list The list of integers describing the position.
 */
case class HOLPosition( list: List[Int] ) {
  require( list.forall( i => i == 1 || i == 2 ) )

  def toList: List[Int] = list
  def head: Int = list.head
  def headOption: Option[Int] = list.headOption
  def tail = HOLPosition( list.tail )
  def isEmpty: Boolean = list.isEmpty
  override def toString = s"[${list.mkString( "," )}]"

  def ::( x: Int ): HOLPosition = HOLPosition( x :: list )

  def isPrefixOf( that: HOLPosition ): Boolean = list match {
    case Nil => true
    case x :: xs => that.list match {
      case Nil     => false
      case y :: ys => ( x == y ) && ( HOLPosition( xs ) isPrefixOf HOLPosition( ys ) )
    }
  }
}

object BinaryConnective {
  def unapply( exp: Expr ): Option[( Formula, Formula )] = exp match {
    case And( l, r ) => Some( l, r )
    case Or( l, r )  => Some( l, r )
    case Imp( l, r ) => Some( l, r )
    case _           => None
  }
}
