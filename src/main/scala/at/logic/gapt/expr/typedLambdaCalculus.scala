/*
 * typedLambdaCalculus.scala
 *
 */

package at.logic.gapt.expr

import at.logic.gapt.language.hol.HOLPosition
import at.logic.gapt.language.hol.HOLPosition._
import symbols._
import types._

// Collects all methods that operate on LambdaExpressions
abstract class LambdaExpression {

  // Expression type [should it be here?]
  def exptype: TA

  def hashCode: Int
  override def equals( a: Any ) = alphaEquals( a, Map[Var, Var]() )

  // Syntactic equality
  def syntaxEquals( e: LambdaExpression ): Boolean

  // Alpha equality
  def alphaEquals( a: Any, subs: Map[Var, Var] ): Boolean

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
    case All( Var( x, Ti ), e )       => s"∀$x.$e"
    case All( Var( x, t ), e )        => s"∀$x:$t.$e"
    case Ex( Var( x, Ti ), e )        => s"∃$x.$e"
    case Ex( Var( x, t ), e )         => s"∃$x:$t.$e"
    case Ands( xs @ Seq( _, _, _* ) ) => s"(${xs mkString "∧"})"
    case Ors( xs @ Seq( _, _, _* ) )  => s"(${xs mkString "∨"})"
    case Imp( x, y )                  => s"($x⊃$y)"
    case Neg( x )                     => s"¬$x"
    case Bottom()                     => "⊥"
    case Top()                        => "⊤"

    case Eq( x, y )                   => s"$x=$y"
    case FOLAtom( r, Seq() )          => s"$r"
    case FOLFunction( f, Seq() )      => s"$f"
    case FOLAtom( r, xs )             => s"$r(${xs mkString ","})"
    case FOLFunction( f, xs )         => s"$f(${xs mkString ","})"

    case Abs( x, t )                  => s"λ$x.$t"
    case App( x, y )                  => s"($x $y)"
    case Var( x, t )                  => s"$x"
    case Const( x, t )                => s"$x"
  }
}

// Defines the elements that generate lambda-expressions: variables,
// applications and abstractions (and constants).

class Var( val sym: SymbolA, val exptype: TA ) extends LambdaExpression {

  // The name of the variable should be obtained with this method.
  def name: String = sym.toString

  // Syntactic equality: two variables are equal if they have the same name and the same type
  def syntaxEquals( e: LambdaExpression ) = e match {
    case Var( n, t ) => ( n == name && t == exptype )
    case _           => false
  }

  // Alpha-equality
  // Two free variables are *not* alpha-equivalent if they don't have the same
  // name and type or if they are not in the substitution list because of a
  // binding.
  def alphaEquals( a: Any, subs: Map[Var, Var] ) = a match {
    case Var( n, t ) if !subs.contains( this )    => ( n == name && t == exptype )
    case v: Var if subs( this ).syntaxEquals( v ) => true
    case _                                        => false
  }

  override def hashCode = 41 * "Var".hashCode + exptype.hashCode
}

class Const( val sym: SymbolA, val exptype: TA ) extends LambdaExpression {

  def name: String = sym.toString

  def syntaxEquals( e: LambdaExpression ) = e match {
    case Const( n, t ) => ( n == name && t == exptype )
    case _             => false
  }

  def alphaEquals( a: Any, subs: Map[Var, Var] ) = a match {
    case Const( n, t ) => n == name && t == exptype
    case _             => false
  }

  override def hashCode() = ( 41 * name.hashCode ) + exptype.hashCode
}

class App( val function: LambdaExpression, val arg: LambdaExpression ) extends LambdaExpression {
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

  def alphaEquals( a: Any, subs: Map[Var, Var] ) = a match {
    case App( e1, e2 ) => e1.alphaEquals( function, subs ) && e2.alphaEquals( arg, subs )
    case _             => false
  }

  override def hashCode() = ( 41 * function.hashCode ) + arg.hashCode
}

class Abs( val variable: Var, val term: LambdaExpression ) extends LambdaExpression {
  val exptype: TA = variable.exptype -> term.exptype

  def syntaxEquals( e: LambdaExpression ) = e match {
    case Abs( v, exp ) => v.syntaxEquals( variable ) && exp.syntaxEquals( term ) && e.exptype == exptype
    case _             => false
  }

  def alphaEquals( a: Any, subs: Map[Var, Var] ) = a match {
    case Abs( v, t ) =>
      if ( v.exptype == variable.exptype ) {
        t.alphaEquals( term, subs + ( variable -> v ) + ( v -> variable ) )
      } else false
    case _ => false
  }

  override def hashCode = 41 * "Abs".hashCode + term.hashCode
}

object Var {
  def apply( name: String, exptype: TA ): Var = Var( StringSymbol( name ), exptype )
  def apply( sym: SymbolA, exptype: TA ): Var = exptype match {
    case Ti => new Var( sym, exptype ) with FOLVar
    case To => new Var( sym, exptype ) with Formula
    case _  => new Var( sym, exptype )
  }
  def unapply( e: LambdaExpression ) = e match {
    case v: Var => Some( v.name, v.exptype )
    case _      => None
  }
}
object Const {
  def apply( name: String, exptype: TA ): Const = Const( StringSymbol( name ), exptype )
  def apply( sym: SymbolA, exptype: TA ): Const = ( sym, exptype ) match {
    case ForallC( Ti ) | ExistsC( Ti ) => new Const( sym, exptype ) with FOLQuantifier
    case AndC() | OrC() | ImpC() => new Const( sym, exptype ) with PropConnective {
      override val numberOfArguments = 2
    }
    case NegC() => new Const( sym, exptype ) with PropConnective {
      override val numberOfArguments = 1
    }
    case TopC() | BottomC() => new Const( sym, exptype ) with PropConnective with PropFormula
    case ( _, Ti )          => new Const( sym, exptype ) with FOLConst
    case ( _, To )          => new Const( sym, exptype ) with PropFormula
    case ( _, FOLHeadType( Ti, n ) ) => new Const( sym, exptype ) with FOLLambdaTerm {
      override val returnType = Ti
      override val numberOfArguments = n
    }
    case ( _, FOLHeadType( To, n ) ) => new Const( sym, exptype ) with PropLambdaTerm {
      override val numberOfArguments = n
    }
    case _ => new Const( sym, exptype )
  }
  def unapply( e: LambdaExpression ) = e match {
    case c: Const => Some( c.name, c.exptype )
    case _        => None
  }
}
object App {
  def apply( f: LambdaExpression, a: LambdaExpression ) = ( f, a ) match {
    case ( f: PropLambdaTerm, a: PropFormula ) => f.numberOfArguments match {
      case 1 => new App( f, a ) with PropFormula
      case n => new App( f, a ) with PropLambdaTerm {
        override val numberOfArguments = n - 1
      }
    }
    case ( f: FOLLambdaTerm, a: FOLExpression ) => f.numberOfArguments match {
      case 1 => f.returnType match {
        case Ti => new App( f, a ) with FOLTerm
        case To => new App( f, a ) with FOLFormula
      }
      case n => new App( f, a ) with FOLLambdaTerm {
        override val numberOfArguments = n - 1
        override val returnType = f.returnType
      }
    }
    case ( f: FOLQuantifier, _ ) => a match {
      case a: FOLFormulaWithBoundVar => new App( f, a ) with FOLFormula
      case _                         => new App( f, a ) with Formula
    }
    case _ => f.exptype match {
      case ->( _, To ) => new App( f, a ) with Formula
      case _           => new App( f, a )
    }
  }

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
  def apply( v: Var, t: LambdaExpression ) = ( v.exptype, t ) match {
    case ( Ti, t: FOLFormula ) => new Abs( v, t ) with FOLFormulaWithBoundVar
    case _                     => new Abs( v, t )
  }
  def apply( variables: List[Var], expression: LambdaExpression ): LambdaExpression = variables match {
    case Nil     => expression
    case x :: ls => Abs( x, apply( ls, expression ) )
  }
  def unapply( e: LambdaExpression ) = e match {
    case a: Abs => Some( ( a.variable, a.term ) )
    case _      => None
  }
}

