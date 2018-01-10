package at.logic.gapt.expr

import at.logic.gapt.expr.hol.HOLPosition
import at.logic.gapt.expr.hol.HOLPosition._
import at.logic.gapt.formats.babel.{ BabelExporter, BabelSignature }

import scala.annotation.tailrec

abstract class Expr {

  /**
   * Type of this expression (e.g. i>i>o).
   */
  def ty: Ty

  def hashCode: Int
  def alphaEquivalentHashCode: Int

  override def equals( a: Any ) = a match {
    case a: AnyRef if this eq a            => true
    case e: Expr if e.hashCode != hashCode => false
    case e: Expr                           => this alphaEquals e
    case _                                 => false
  }

  /**
   * Syntactic equality (takes names of variables in binders into account).
   */
  def syntaxEquals( e: Expr ): Boolean

  /**
   * Alpha-equality.
   *
   * @param that  Lambda expression to compare against.
   * @return whether this lambda expression is equal to that lambda expression modulo alpha-conversion.
   */
  def alphaEquals( that: Expr ): Boolean = this alphaEquals ( that, 0, Map(), Map() )

  /**
   * Alpha-equality in a bound variable context.
   *
   * The parameters thisCtx and thatCtx list the bound variables in the corresponding lambda expressions,
   * together with indices that indicate the originating binder.  That is, two bound variables `x` and `y`
   * (in this and that, respectively) are alpha-equal iff `thisCtx(x) == thatCtx(y)`.
   *
   * @param that  Lambda expression to compare against.
   * @param lcBound Upper bound for the values in thisCtx and thatCtx ("local constant bound").
   * @param thisCtx Bound variables in this lambda expression.
   * @param thatCtx Bound variables in that lambda expression.
   * @return whether thisCtx(this) is alpha-equal to thatCtx(that)
   */
  private[expr] def alphaEquals( that: Expr, lcBound: Int, thisCtx: Map[Var, Int], thatCtx: Map[Var, Int] ): Boolean

  /**
   * Tests whether this Expression has a subexpression at the given position.
   */
  def isDefinedAt( p: LambdaPosition ): Boolean = p.isDefined( this )

  /**
   * Returns the subexpression at the given position, if it exists.
   */
  def get( p: LambdaPosition ): Option[Expr] = p.get( this )

  def apply( p: LambdaPosition ): Expr = get( p ) match {
    case Some( e ) => e
    case None      => throw new IllegalArgumentException( "Expression " + this + "is not defined at position " + p + "." )
  }
  /**
   * Retrieves this expression's subexpression at a given position.
   *
   * @param pos The position to be retrieved.
   * @return The subexpression at pos.
   */
  def apply( pos: HOLPosition ): Expr = get( pos ) match {
    case Some( f ) => f
    case None      => throw new Exception( "Position " + pos + " does not exist in expression " + this + "." )
  }

  /**
   * Retrieves this expression's subexpression at a given position, if there is one.
   *
   * @param pos The position to be retrieved.
   * @return If there is a subexpression at that position, return Some(that expression). Otherwise None.
   */
  def get( pos: HOLPosition ): Option[Expr] =
    HOLPosition.toLambdaPositionOption( this )( pos ).flatMap( get )

  def replace( pos: LambdaPosition, replacement: Expr ): Expr =
    LambdaPosition.replace( this, pos, replacement )

  def replace( pos: HOLPosition, replacement: Expr ): Expr =
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
  def find( exp: Expr ): List[HOLPosition] = getPositions( this, _ == exp )

  /**
   * Tests whether an expression is a subexpression.
   *
   * @param exp The subexpression to be found.
   * @return A boolean that is true if exp is a subexpression
   */
  def contains( exp: Expr ): Boolean = find( exp ).nonEmpty

  /**
   * Converts this expression into a string.
   *
   * The output can be parsed using e.g. the string interpolators, and we
   * guarantee that the expression can be perfectly reconstructed from the string output.
   */
  override def toString = new BabelExporter( unicode = true, sig = BabelSignature.defaultSignature ).export( this )
  /**
   * Converts this expression into a 7-bit safe ASCII string.
   *
   * The output can be parsed using e.g. the string interpolators, and we
   * guarantee that the expression can be perfectly reconstructed from the string output.
   */
  def toAsciiString = new BabelExporter( unicode = false, sig = BabelSignature.defaultSignature ).export( this )
  /**
   * Converts this expression into a string, taking the signature into account.
   *
   * This produces a similar output as [[toString]], but will use the
   * variable convention indicated by the signature.  That is, if sig defines x to
   * be a constant, then we output just x instead of the default #c(x: i).
   */
  def toSigRelativeString( implicit sig: BabelSignature ) =
    new BabelExporter( unicode = true, sig = sig ).export( this )

  def toUntypedString( implicit sig: BabelSignature ) =
    new BabelExporter( unicode = true, sig = implicitly, omitTypes = true ).export( this )
  def toUntypedAsciiString( implicit sig: BabelSignature ) =
    new BabelExporter( unicode = false, sig = implicitly, omitTypes = true ).export( this )

  def &( that: Expr ): Formula = And( this, that )
  def |( that: Expr ): Formula = Or( this, that )
  def unary_- : Formula = Neg( this )
  def -->( that: Expr ) = Imp( this, that )
  def <->( that: Expr ) = And( Imp( this, that ), Imp( that, this ) )
  def ===( that: Expr ) = Eq( this, that )
  def !==( that: Expr ) = Neg( Eq( this, that ) )
  def apply( that: Expr* ): Expr = App( this, that )
  def apply( that: Iterable[Expr] ): Expr = App( this, that.toSeq )

  def ^( n: Int )( that: Expr ): Expr =
    if ( n == 0 ) that else ( this ^ ( n - 1 ) )( this( that ) )
}

class Var private[expr] ( val name: String, val ty: Ty ) extends VarOrConst {
  def syntaxEquals( e: Expr ) = e match {
    case Var( n, t ) => n == name && t == ty
    case _           => false
  }

  private[expr] override def alphaEquals(
    that:    Expr,
    lcBound: Int, thisCtx: Map[Var, Int], thatCtx: Map[Var, Int] ): Boolean =
    that match {
      case that: Var =>
        ( thisCtx.getOrElse( this, -1 ), thatCtx.getOrElse( that, -1 ) ) match {
          case ( -1, -1 )         => this syntaxEquals that // not bound
          case ( i, j ) if i == j => true // both bound to the same local constant
          case _                  => false
        }
      case _ => false
    }

  override val hashCode = 42 * name.hashCode + ty.hashCode
  override val alphaEquivalentHashCode = 42 + ty.hashCode
}

class Const private[expr] ( val name: String, val ty: Ty, val params: List[Ty] ) extends VarOrConst {

  def syntaxEquals( e: Expr ) = e match {
    case Const( n, t, ps ) => n == name && t == ty && ps == params
    case _                 => false
  }

  private[expr] override def alphaEquals( that: Expr, lcBound: Int, thisCtx: Map[Var, Int], thatCtx: Map[Var, Int] ) =
    this syntaxEquals that

  override val hashCode = ( 41 * name.hashCode ) + ty.hashCode
  override def alphaEquivalentHashCode = hashCode
}

class App private[expr] ( val function: Expr, val arg: Expr ) extends Expr {
  val ty: Ty =
    function.ty match {
      case in ->: out if in == arg.ty => out
      case _ => throw new IllegalArgumentException(
        s"Types don't fit while constructing application ($function : ${function.ty}) ($arg : ${arg.ty})" )
    }

  def syntaxEquals( e: Expr ) = e match {
    case App( a, b ) => e.ty == ty &&
      a.syntaxEquals( function ) && b.syntaxEquals( arg )
    case _ => false
  }

  private[expr] override def alphaEquals(
    that:    Expr,
    lcBound: Int, thisCtx: Map[Var, Int], thatCtx: Map[Var, Int] ) =
    that match {
      case App( that_function, that_arg ) =>
        this.function.alphaEquals( that_function, lcBound, thisCtx, thatCtx ) &&
          this.arg.alphaEquals( that_arg, lcBound, thisCtx, thatCtx )
      case _ => false
    }

  override val hashCode = ( 41 * function.hashCode ) + arg.hashCode
  override val alphaEquivalentHashCode = ( 41 * function.alphaEquivalentHashCode ) + arg.alphaEquivalentHashCode
}

class Abs private[expr] ( val variable: Var, val term: Expr ) extends Expr {
  val ty: Ty = variable.ty ->: term.ty

  def syntaxEquals( e: Expr ) = e match {
    case Abs( v, exp ) => v.syntaxEquals( variable ) && exp.syntaxEquals( term ) && e.ty == ty
    case _             => false
  }

  private[expr] override def alphaEquals(
    that:    Expr,
    lcBound: Int, thisCtx: Map[Var, Int], thatCtx: Map[Var, Int] ) =
    that match {
      case Abs( that_variable, that_term ) if this.variable.ty == that_variable.ty =>
        this.term.alphaEquals( that_term, lcBound + 1,
          thisCtx.updated( this.variable, lcBound ),
          thatCtx.updated( that_variable, lcBound ) )
      case _ => false
    }

  override val hashCode = 41 * term.alphaEquivalentHashCode + variable.ty.hashCode
  override def alphaEquivalentHashCode = hashCode
}

object Var {
  def apply( name: String, exptype: Ty ): Var = determineTraits.forVar( name, exptype )

  def unapply( v: Var ): Some[( String, Ty )] = Some( v.name, v.ty )
}
object Const {
  def apply( name: String, exptype: Ty, params: List[Ty] = Nil ): Const =
    determineTraits.forConst( name, exptype, params )

  def unapply( c: Const ): Some[( String, Ty, List[Ty] )] = Some( ( c.name, c.ty, c.params ) )
}
object App {
  def apply( f: Expr, a: Expr ) = determineTraits.forApp( f, a )

  def apply( function: Expr, arguments: Seq[Expr] ): Expr = Apps( function, arguments )

  def unapply( a: App ): Some[( Expr, Expr )] = Some( a.function, a.arg )
}
object Apps {
  def apply( function: Expr, arguments: Expr* )( implicit dummyImplicit: DummyImplicit ): Expr =
    apply( function, arguments )

  /** Create an n-ary application with left-associative parentheses. */
  def apply( function: Expr, arguments: Seq[Expr] ): Expr =
    arguments.foldLeft( function )( App( _, _ ) )

  def unapply( e: Expr ): Some[( Expr, List[Expr] )] =
    Some( decompose( e, Nil ) )

  @tailrec
  private def decompose( e: Expr, restArgs: List[Expr] ): ( Expr, List[Expr] ) =
    e match {
      case App( head, arg ) => decompose( head, arg :: restArgs )
      case head             => ( head, restArgs )
    }
}
object Abs {
  def apply( v: Var, t: Expr ) = determineTraits.forAbs( v, t )
  def apply( variables: Seq[Var], expression: Expr ): Expr =
    variables.foldRight( expression )( Abs( _, _ ) )

  def unapply( a: Abs ): Some[( Var, Expr )] = Some( a.variable, a.term )

  object Block {
    def apply( vars: Seq[Var], expr: Expr ) = Abs( vars, expr )
    def unapply( e: Expr ): Some[( List[Var], Expr )] = e match {
      case Abs( v, e_ ) => e_ match { case Block( vs, e__ ) => Some( ( v :: vs, e__ ) ) }
      case e_           => Some( ( Nil, e_ ) )
    }
  }
}

