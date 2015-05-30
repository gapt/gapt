/*
 * typedLambdaCalculus.scala
 *
 */

package at.logic.gapt.expr

import at.logic.gapt.language.hol.HOLPosition
import at.logic.gapt.language.hol.HOLPosition._

// Collects all methods that operate on LambdaExpressions
abstract class LambdaExpression {

  // Expression type [should it be here?]
  def exptype: TA

  def hashCode: Int
  override def equals( a: Any ) = a match {
    case e: LambdaExpression => this alphaEquals e
    case _                   => false
  }

  // Syntactic equality
  def syntaxEquals( e: LambdaExpression ): Boolean

  /**
   * Alpha-equality.
   *
   * @param that  Lambda expression to compare against.
   * @return whether this lambda expression is equal to that lambda expression modulo alpha-conversion.
   */
  def alphaEquals( that: LambdaExpression ): Boolean = this alphaEquals ( that, List(), List() )

  /**
   * Alpha-equality in a bound variable context.
   *
   * The parameters thisCtx and thatCtx list the bound variables in the corresponding lambda expressions, they can be
   * thought of as maps from DeBruijn indices to their bound variables.  If we invert this map and extend it to
   * non-bound variables as the identity, then the inverse map renames bound variables to new fresh variables (actually
   * numbers).
   *
   * @param that  Lambda expression to compare against.
   * @param thisCtx Bound variables in this lambda expression.
   * @param thatCtx Bound variables in that lambda expression.
   * @return whether thisCtx^{-1}(this) is alpha-equal to thatCtx^{-1}(that)
   */
  private[expr] def alphaEquals( that: LambdaExpression, thisCtx: List[Var], thatCtx: List[Var] ): Boolean

  /**
   * Tests whether this Expression has a subexpression at the given position.
   *
   * @param p
   * @return
   */
  def isDefinedAt( p: LambdaPosition ): Boolean = p.isDefined( this )

  /**
   * Returns the subexpression at the given position, if it exists.
   *
   * @param p
   * @return
   */
  def get( p: LambdaPosition ): Option[LambdaExpression] = p.get( this )

  def apply( p: LambdaPosition ): LambdaExpression = get( p ) match {
    case Some( e ) => e
    case None      => throw new IllegalArgumentException( "Expression " + this + "is not defined at position " + p + "." )
  }
  /**
   * Retrieves this expression's subexpression at a given position.
   *
   * @param pos The position to be retrieved.
   * @return The subexpression at pos.
   */
  def apply( pos: HOLPosition ): LambdaExpression = get( pos ) match {
    case Some( f ) => f
    case None      => throw new Exception( "Position " + pos + " does not exist in expression " + this + "." )
  }

  /**
   * Retrieves this expression's subexpression at a given position, if there is one.
   *
   * @param pos The position to be retrieved.
   * @return If there is a subexpression at that position, return Some(that expression). Otherwise None.
   */
  def get( pos: HOLPosition ): Option[LambdaExpression] = {
    val lPos = toLambdaPosition( this )( pos )
    get( lPos )
  }

  def replace( pos: LambdaPosition, replacement: LambdaExpression ): LambdaExpression =
    LambdaPosition.replace( this, pos, replacement )

  def replace( pos: HOLPosition, replacement: LambdaExpression ): LambdaExpression =
    HOLPosition.replace( this, pos, replacement )

  /**
   * Tests whether this expression has a subexpression at a given position.
   *
   * @param pos The position to be tested.
   * @return Whether this(pos) is defined.
   */
  def isDefinedAt( pos: HOLPosition ): Boolean = get( pos ).isDefined

  /**
   * Finds all HOL positions of a subexpression in this expression.
   *
   * @param exp The subexpression to be found.
   * @return A list containing all positions where exp occurs.
   */
  def find( exp: LambdaExpression ): List[HOLPosition] = getPositions( this, _ == exp )

  override def toString = this match {
    case All( Var( x, Ti ), e )           => s"∀$x.$e"
    case All( Var( x, t ), e )            => s"∀$x:$t.$e"
    case Ex( Var( x, Ti ), e )            => s"∃$x.$e"
    case Ex( Var( x, t ), e )             => s"∃$x:$t.$e"
    case And.nAry( xs @ Seq( _, _, _* ) ) => s"(${xs mkString "∧"})"
    case Or.nAry( xs @ Seq( _, _, _* ) )  => s"(${xs mkString "∨"})"
    case Imp( x, y )                      => s"($x⊃$y)"
    case Neg( x )                         => s"¬$x"
    case Bottom()                         => "⊥"
    case Top()                            => "⊤"

    case Eq( x, y )                       => s"$x=$y"
    case FOLAtom( r, Seq() )              => s"$r"
    case FOLFunction( f, Seq() )          => s"$f"
    case FOLAtom( r, xs )                 => s"$r(${xs mkString ","})"
    case FOLFunction( f, xs )             => s"$f(${xs mkString ","})"

    case Abs( x, t )                      => s"λ$x.$t"
    case App( x, y )                      => s"($x $y)"
    case Var( x, t )                      => s"$x"
    case Const( x, t )                    => s"$x"
  }
}

// Defines the elements that generate lambda-expressions: variables,
// applications and abstractions (and constants).

class Var private[expr] ( val sym: SymbolA, val exptype: TA ) extends LambdaExpression {

  // The name of the variable should be obtained with this method.
  def name: String = sym.toString

  // Syntactic equality: two variables are equal if they have the same name and the same type
  def syntaxEquals( e: LambdaExpression ) = e match {
    case Var( n, t ) => ( n == name && t == exptype )
    case _           => false
  }

  private[expr] override def alphaEquals( that: LambdaExpression, thisCtx: List[Var], thatCtx: List[Var] ): Boolean =
    ( thisCtx indexOf this, thatCtx indexOf that ) match {
      case ( -1, -1 )         => this syntaxEquals that // not bound
      case ( i, j ) if i == j => true // both bound to the same DeBruijn index
      case _                  => false
    }

  override def hashCode = 41 * "Var".hashCode + exptype.hashCode
}

class Const private[expr] ( val sym: SymbolA, val exptype: TA ) extends LambdaExpression {

  def name: String = sym.toString

  def syntaxEquals( e: LambdaExpression ) = e match {
    case Const( n, t ) => ( n == name && t == exptype )
    case _             => false
  }

  private[expr] override def alphaEquals( that: LambdaExpression, thisCtx: List[Var], thatCtx: List[Var] ) =
    this syntaxEquals that

  override def hashCode() = ( 41 * name.hashCode ) + exptype.hashCode
}

class App private[expr] ( val function: LambdaExpression, val arg: LambdaExpression ) extends LambdaExpression {
  val exptype: TA =
    function.exptype match {
      case ( in -> out ) if in == arg.exptype => out
      case _ => throw new IllegalArgumentException(
        s"Types don't fit while constructing application ($function : ${function.exptype}) ($arg : ${arg.exptype})" )
    }

  def syntaxEquals( e: LambdaExpression ) = e match {
    case App( a, b ) => ( a.syntaxEquals( function ) && b.syntaxEquals( arg ) && e.exptype == exptype )
    case _           => false
  }

  private[expr] override def alphaEquals( that: LambdaExpression, thisCtx: List[Var], thatCtx: List[Var] ) = that match {
    case App( that_function, that_arg ) =>
      this.function.alphaEquals( that_function, thisCtx, thatCtx ) &&
        this.arg.alphaEquals( that_arg, thisCtx, thatCtx )
    case _ => false
  }

  override def hashCode() = ( 41 * function.hashCode ) + arg.hashCode
}

class Abs private[expr] ( val variable: Var, val term: LambdaExpression ) extends LambdaExpression {
  val exptype: TA = variable.exptype -> term.exptype

  def syntaxEquals( e: LambdaExpression ) = e match {
    case Abs( v, exp ) => v.syntaxEquals( variable ) && exp.syntaxEquals( term ) && e.exptype == exptype
    case _             => false
  }

  private[expr] override def alphaEquals( that: LambdaExpression, thisCtx: List[Var], thatCtx: List[Var] ) = that match {
    case Abs( that_variable, that_term ) if this.variable.exptype == that_variable.exptype =>
      this.term alphaEquals ( that_term, this.variable :: thisCtx, that_variable :: thatCtx )
    case _ => false
  }

  override def hashCode = 41 * "Abs".hashCode + term.hashCode
}

object Var {
  def apply( name: String, exptype: TA ): Var = Var( StringSymbol( name ), exptype )
  def apply( sym: SymbolA, exptype: TA ): Var = determineTraits.forVar( sym, exptype )

  def unapply( e: LambdaExpression ) = e match {
    case v: Var => Some( v.name, v.exptype )
    case _      => None
  }
}
object Const {
  def apply( name: String, exptype: TA ): Const = Const( StringSymbol( name ), exptype )
  def apply( sym: SymbolA, exptype: TA ): Const = determineTraits.forConst( sym, exptype )

  def unapply( e: LambdaExpression ) = e match {
    case c: Const => Some( c.name, c.exptype )
    case _        => None
  }
}
object App {
  def apply( f: LambdaExpression, a: LambdaExpression ) = determineTraits.forApp( f, a )

  @deprecated( "This constructor has moved to Apps" )
  def apply( function: LambdaExpression, arguments: List[LambdaExpression] ): LambdaExpression = Apps( function, arguments )

  def unapply( e: LambdaExpression ) = e match {
    case a: App => Some( ( a.function, a.arg ) )
    case _      => None
  }
}
object Apps {
  def apply( function: LambdaExpression, arguments: LambdaExpression* ): LambdaExpression =
    apply( function, arguments toList )

  // create an n-ary application with left-associative parentheses
  def apply( function: LambdaExpression, arguments: List[LambdaExpression] ): LambdaExpression = arguments match {
    case Nil     => function
    case x :: ls => apply( App( function, x ), ls )
  }

  def unapply( e: LambdaExpression ): Some[( LambdaExpression, List[LambdaExpression] )] = e match {
    case App( Apps( hd, args ), arg ) => Some( ( hd, args ::: List( arg ) ) )
    case e                            => Some( ( e, List() ) )
  }
}
object Abs {
  def apply( v: Var, t: LambdaExpression ) = determineTraits.forAbs( v, t )
  def apply( variables: List[Var], expression: LambdaExpression ): LambdaExpression = variables match {
    case Nil     => expression
    case x :: ls => Abs( x, apply( ls, expression ) )
  }

  def unapply( e: LambdaExpression ) = e match {
    case a: Abs => Some( ( a.variable, a.term ) )
    case _      => None
  }
}

