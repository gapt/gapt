/**
 * This file contains code for positions and replacements in Exprs.
 *
 */

package gapt.expr.util

import gapt.expr.Abs
import gapt.expr.App
import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.Var
import gapt.expr.util.LambdaPosition.Choice

object LambdaPosition {

  trait Choice
  case object Left extends Choice
  case object Right extends Choice

  /**
   * Returns a list of positions of subexpressions that satisfy some predicate.
   *
   * @param expression The expression under consideration.
   * @param predicate The predicate to be evaluated.
   * @return Positions of subexpressions satisfying the predicate.
   */
  def filterPositions( predicate: Expr => Boolean )( expression: Expr ): List[LambdaPosition] =
    getPositions( expression )
      .map { p => p -> expression( p ) }
      .filter { case ( _, e ) => predicate( e ) }
      .map { _._1 }

  /**
   * Retrieves all subterm positions of a term.
   *
   * @param expression The expression whose subterm positions are to be computed.
   * @return All subterm positions of the given expression.
   */
  def getPositions( expression: Expr ): List[LambdaPosition] =
    expression match {
      case App( e1, e2 ) =>
        val leftPositions = getPositions( e1 ).map { Left :: _ }
        val rightPositions = getPositions( e2 ).map { Right :: _ }
        List( LambdaPosition() ) ++ leftPositions ++ rightPositions
      case Abs( _, e ) =>
        val subtermPositions = getPositions( e ).map { Left :: _ }
        List( LambdaPosition() ) ++ subtermPositions
      case _ => List( LambdaPosition() )
    }

  /**
   * Compares to Exprs and returns the list of outermost positions where they differ.
   *
   * @param exp1 The first expression.
   * @param exp2 The second expression.
   * @return The list of outermost positions at which exp1 and exp2 differ.
   */
  def differingPositions( exp1: Expr, exp2: Expr ): List[LambdaPosition] =
    ( exp1, exp2 ) match {
      case ( Var( n1, t1 ), Var( n2, t2 ) ) if n1 == n2 && t1 == t2 => Nil
      case ( c1: Const, c2: Const ) if c1 == c2                     => Nil
      case ( App( f1, arg1 ), App( f2, arg2 ) ) =>
        val list1 = differingPositions( f1, f2 ) map { p => Left :: p }
        val list2 = differingPositions( arg1, arg2 ) map { p => Right :: p }
        list1 ++ list2
      case ( Abs( v1, term1 ), Abs( v2, term2 ) ) if v1 == v2 =>
        differingPositions( term1, term2 ) map { p => Left :: p }
      case _ => List( LambdaPosition() )
    }

  /**
   * Replaces a a subexpression in a Expr.
   *
   * @param exp The expression in which to perform the replacement.
   * @param pos The position at which to replace.
   * @param repTerm The expression that exp(pos) should be replaced with.
   * @return
   */
  def replace( exp: Expr, pos: LambdaPosition, repTerm: Expr ): Expr =
    if ( pos.isEmpty )
      repTerm
    else {
      val rest = pos.tail
      exp match {
        case Abs( t, subExp ) if pos.head == LambdaPosition.Left =>
          Abs( t, replace( subExp, rest, repTerm ) )
        case App( f, arg ) if pos.head == LambdaPosition.Left =>
          App( replace( f, rest, repTerm ), arg )
        case App( f, arg ) if pos.head == LambdaPosition.Right =>
          App( f, replace( arg, rest, repTerm ) )
        case _ => throw new IllegalArgumentException(
          "Not possible to replace at position " + pos + " in expression " + exp + "." )
      }
    }

  def apply( xs: Choice* ) = new LambdaPosition( xs.toList )
  def toList( p: LambdaPosition ): List[Choice] = p.list
}

/**
 * Represents a position in a [[gapt.expr.Expr]].
 *
 * Positions are represented by lists of Integers. The empty list denotes the expression itself.
 * A nonempty list denotes a position in the left or right subexpression according to whether it starts with 1 or 2.
 *
 * @param list The list of integers describing the position.
 */
case class LambdaPosition( list: List[Choice] ) {

  def toList: List[Choice] = list
  def head: Choice = list.head
  def headOption: Option[Choice] = list.headOption
  def tail: LambdaPosition = LambdaPosition( list.tail )
  def isEmpty: Boolean = list.isEmpty
  override def toString = s"[${list.mkString( "," )}]"

  def ::( x: Choice ): LambdaPosition = LambdaPosition( x :: list )

  def isDefined( exp: Expr ): Boolean = get( exp ).isDefined

  def get( exp: Expr ): Option[Expr] = exp match {
    case _ if isEmpty => Some( exp )
    case App( f, a ) if head == LambdaPosition.Left => tail.get( f )
    case App( f, a ) if head == LambdaPosition.Right => tail.get( a )
    case Abs( v, t ) if head == LambdaPosition.Left => tail.get( t )
    case _ => None
  }
}