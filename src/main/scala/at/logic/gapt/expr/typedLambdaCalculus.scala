/*
 * typedLambdaCalculus.scala
 *
 */

package at.logic.gapt.expr

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

class Const private[expr] ( val sym: SymbolA, val exptype: TA ) extends LambdaExpression {

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
    case Ti     => new Var( sym, exptype ) with FOLVar
    case Tindex => new Var( sym, exptype ) with SchematicVar
    case To     => new Var( sym, exptype ) with Formula
    case _      => new Var( sym, exptype )
  }
  def unapply( e: LambdaExpression ) = e match {
    case v: Var => Some( v.name, v.exptype )
    case _      => None
  }
}
object Const {
  import schematic._

  def apply( name: String, exptype: TA ): Const = Const( StringSymbol( name ), exptype )
  def apply( sym: SymbolA, exptype: TA ): Const = ( sym, exptype ) match {
    case ForallQ( Ti ) | ExistsQ( Ti ) => new Const( sym, exptype ) with FOLQuantifier
    case AndC() | OrC() | ImpC() => new Const( sym, exptype ) with PropConnective {
      override val numberOfArguments = 2
    }
    case NegC() => new Const( sym, exptype ) with PropConnective {
      override val numberOfArguments = 1
    }
    case TopC() | BottomC()   => new Const( sym, exptype ) with PropConnective with PropFormula
    case BigAndC() | BigOrC() => new Const( sym, exptype ) with SchematicBigConnective
    case EqC( Ti ) => new Const( sym, exptype ) with FOLLambdaTerm with DistinguishedConstant {
      override val returnType = Ti
      override val numberOfArguments = 2
    }
    case EqC( Tindex ) => new Const( sym, exptype ) with SchematicLambdaTerm with DistinguishedConstant {
      override val returnType = Ti
      override val numberOfArguments = 2
    }
    case EqC( _ ) => new Const( sym, exptype ) with DistinguishedConstant
    case ZeroC()  => new Const( sym, exptype ) with SchematicIntTerm
    case SuccC() => new Const( sym, exptype ) with SchematicLambdaTerm {
      override val returnType = Tindex
      override val numberOfArguments = 1
    }
    case PlusC() | TimesC() => new Const( sym, exptype ) with SchematicLambdaTerm {
      override val returnType = Tindex
      override val numberOfArguments = 2
    }
    case BiggerThanC() | SimC() | LessThanC() | LeqC() => new Const( sym, exptype ) with SchematicLambdaTerm {
      override val returnType = To
      override val numberOfArguments = 2
    }
    case ( _, Ti ) => new Const( sym, exptype ) with FOLTerm
    case ( _, To ) => new Const( sym, exptype ) with PropFormula
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
  def apply( f: LambdaExpression, a: LambdaExpression ) = f match {
    case f: PropLambdaTerm => f.numberOfArguments match {
      case 1 => new App( f, a ) with PropFormula
      case n => new App( f, a ) with PropLambdaTerm {
        override val numberOfArguments = n - 1
      }
    }
    case f: FOLLambdaTerm => f.numberOfArguments match {
      case 1 => f.returnType match {
        case Ti => new App( f, a ) with FOLTerm
        case To => new App( f, a ) with FOLFormula
      }
      case n => new App( f, a ) with FOLLambdaTerm {
        override val numberOfArguments = n - 1
        override val returnType = f.returnType
      }
    }
    case f: SchematicLambdaTerm => f.numberOfArguments match {
      case 1 => f.returnType match {
        case Tindex => new App( f, a ) with SchematicIntTerm
        case Ti     => new App( f, a ) with SchematicTerm
        case To     => new App( f, a ) with SchematicFormula
      }
      case n => new App( f, a ) with SchematicLambdaTerm {
        override val numberOfArguments = n - 1
        override val returnType = f.returnType
      }
    }
    case f: FOLQuantifier => a match {
      case a: FOLFormulaWithBoundVar       => new App( f, a ) with FOLFormula
      case a: SchematicFormulaWithBoundVar => new App( f, a ) with SchematicFormula
      case _                               => new App( f, a ) with Formula
    }
    case f: SchematicBigConnective => a match {
      case a: SchematicFormulaWithBoundIndex => new App( f, a ) with SchematicLambdaTerm {
        override val numberOfArguments = 2
        override val returnType = To
      }
      case _ => new App( f, a )
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
    case ( Ti, t: FOLFormula )           => new Abs( v, t ) with FOLFormulaWithBoundVar
    case ( Ti, t: SchematicFormula )     => new Abs( v, t ) with SchematicFormulaWithBoundVar
    case ( Tindex, t: SchematicFormula ) => new Abs( v, t ) with SchematicFormulaWithBoundIndex
    case _                               => new Abs( v, t )
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

