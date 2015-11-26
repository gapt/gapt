/*
 * typedLambdaCalculus.scala
 *
 */

package at.logic.gapt.expr

import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.expr.hol.HOLPosition._

import scala.annotation.tailrec

// Collects all methods that operate on LambdaExpressions
abstract class LambdaExpression {

  // Expression type [should it be here?]
  def exptype: Ty

  def hashCode: Int
  override def equals( a: Any ) = a match {
    case a: AnyRef if this eq a => true
    case e: LambdaExpression if e.hashCode != hashCode => false
    case e: LambdaExpression => this alphaEquals e
    case _ => false
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
  def get( pos: HOLPosition ): Option[LambdaExpression] =
    HOLPosition.toLambdaPositionOption( this )( pos ).flatMap( get )

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
    case Eq( x, y )                          => s"$x=$y"
    case Neg( Eq( x, y ) )                   => s"$x≠$y"
    case FOLFunction( "+", Seq( x, y ) )     => s"($x+$y)"
    case FOLFunction( "*", Seq( x, y ) )     => s"($x*$y)"

    case All( Var( x, Ti ), e )              => s"∀$x.$e"
    case All( Var( x, t ), e )               => s"∀$x:$t.$e"
    case Ex( Var( x, Ti ), e )               => s"∃$x.$e"
    case Ex( Var( x, t ), e )                => s"∃$x:$t.$e"
    case And( x, y )                         => s"($x∧$y)"
    case Or( x, y )                          => s"($x∨$y)"
    case Imp( x, y )                         => s"($x⊃$y)"
    case Neg( x )                            => s"¬$x"
    case Bottom()                            => "⊥"
    case Top()                               => "⊤"

    case FOLAtom( r, Seq() )                 => s"$r"
    case FOLFunction( f, Seq() )             => s"$f"
    case HOLAtom( r, xs ) if xs.nonEmpty     => s"$r(${xs mkString ","})"
    case HOLFunction( f, xs ) if xs.nonEmpty => s"$f(${xs mkString ","})"

    case Abs( Var( x, Ti ), t )              => s"(λ$x.$t)"
    case Abs( Var( x, ty ), t )              => s"(λ$x:$ty.$t)"
    case App( x, y )                         => s"($x $y)"
    case Var( x, t )                         => s"$x"
    case Const( x, t )                       => s"$x"
  }

  def &( that: LambdaExpression ): HOLFormula = And( this, that )
  def |( that: LambdaExpression ): HOLFormula = Or( this, that )
  def unary_- : HOLFormula = Neg( this )
  def -->( that: LambdaExpression ) = Imp( this, that )
  def <->( that: LambdaExpression ) = And( Imp( this, that ), Imp( that, this ) )
  def ===( that: LambdaExpression ) = Eq( this, that )
  def apply( that: LambdaExpression* ) = App( this, that )
}

// Defines the elements that generate lambda-expressions: variables,
// applications and abstractions (and constants).

class Var private[expr] ( val sym: SymbolA, val exptype: Ty ) extends LambdaExpression {

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

  override val hashCode = 41 * "Var".hashCode + exptype.hashCode
}

class Const private[expr] ( val sym: SymbolA, val exptype: Ty ) extends LambdaExpression {

  def name: String = sym.toString

  def syntaxEquals( e: LambdaExpression ) = e match {
    case Const( n, t ) => ( n == name && t == exptype )
    case _             => false
  }

  private[expr] override def alphaEquals( that: LambdaExpression, thisCtx: List[Var], thatCtx: List[Var] ) =
    this syntaxEquals that

  override val hashCode = ( 41 * name.hashCode ) + exptype.hashCode
}

class App private[expr] ( val function: LambdaExpression, val arg: LambdaExpression ) extends LambdaExpression {
  val exptype: Ty =
    function.exptype match {
      case ( in -> out ) if in == arg.exptype => out
      case _ => throw new IllegalArgumentException(
        s"Types don't fit while constructing application ($function : ${function.exptype}) ($arg : ${arg.exptype})"
      )
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

  override val hashCode = ( 41 * function.hashCode ) + arg.hashCode
}

class Abs private[expr] ( val variable: Var, val term: LambdaExpression ) extends LambdaExpression {
  val exptype: Ty = variable.exptype -> term.exptype

  def syntaxEquals( e: LambdaExpression ) = e match {
    case Abs( v, exp ) => v.syntaxEquals( variable ) && exp.syntaxEquals( term ) && e.exptype == exptype
    case _             => false
  }

  private[expr] override def alphaEquals( that: LambdaExpression, thisCtx: List[Var], thatCtx: List[Var] ) = that match {
    case Abs( that_variable, that_term ) if this.variable.exptype == that_variable.exptype =>
      this.term alphaEquals ( that_term, this.variable :: thisCtx, that_variable :: thatCtx )
    case _ => false
  }

  override val hashCode = 41 * "Abs".hashCode + term.hashCode
}

object Var {
  def apply( name: String, exptype: Ty ): Var = Var( StringSymbol( name ), exptype )
  def apply( sym: SymbolA, exptype: Ty ): Var = determineTraits.forVar( sym, exptype )

  def unapply( v: Var ) = Some( v.name, v.exptype )
}
object Const {
  def apply( name: String, exptype: Ty ): Const = Const( StringSymbol( name ), exptype )
  def apply( sym: SymbolA, exptype: Ty ): Const = determineTraits.forConst( sym, exptype )

  def unapply( c: Const ) = Some( c.name, c.exptype )
}
object App {
  def apply( f: LambdaExpression, a: LambdaExpression ) = determineTraits.forApp( f, a )

  def apply( function: LambdaExpression, arguments: Seq[LambdaExpression] ): LambdaExpression = Apps( function, arguments )

  def unapply( a: App ) = Some( a.function, a.arg )
}
object Apps {
  def apply( function: LambdaExpression, arguments: LambdaExpression* )( implicit dummyImplicit: DummyImplicit ): LambdaExpression =
    apply( function, arguments )

  // create an n-ary application with left-associative parentheses
  def apply( function: LambdaExpression, arguments: Seq[LambdaExpression] ): LambdaExpression =
    arguments.foldLeft( function )( App( _, _ ) )

  def unapply( e: LambdaExpression ): Some[( LambdaExpression, List[LambdaExpression] )] =
    Some( decompose( e, Nil ) )

  @tailrec
  private def decompose( e: LambdaExpression, restArgs: List[LambdaExpression] ): ( LambdaExpression, List[LambdaExpression] ) =
    e match {
      case App( head, arg ) => decompose( head, arg :: restArgs )
      case head             => ( head, restArgs )
    }
}
object Abs {
  def apply( v: Var, t: LambdaExpression ) = determineTraits.forAbs( v, t )
  def apply( variables: Seq[Var], expression: LambdaExpression ): LambdaExpression =
    variables.foldRight( expression )( Abs( _, _ ) )

  def unapply( a: Abs ) = Some( a.variable, a.term )
}

