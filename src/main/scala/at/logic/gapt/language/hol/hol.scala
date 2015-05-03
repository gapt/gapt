/*
 * hol.scala
 */

package at.logic.gapt.language.hol

import at.logic.gapt.language.hol.HOLPosition._
import at.logic.gapt.language.hol.logicSymbols._
import at.logic.gapt.language.lambda.symbols.StringSymbol
import at.logic.gapt.language.lambda.types._
import at.logic.gapt.language.lambda.{ FactoryA, LambdaExpression }

import scala.collection.mutable

trait HOLExpression extends LambdaExpression {

  // map from symbol name to pair of Arity and replacement symbol name
  type SymbolMap = Map[String, ( Int, String )]
  val emptySymbolMap = Map[String, ( Int, String )]()

  // Factory for App, Abs and Var
  override def factory: FactoryA = HOLFactory

  // How many toString methods does one need??
  override def toString = this match {
    case HOLVar( x, tpe )   => x.toString + ":" + tpe.toString
    case HOLConst( x, tpe ) => x.toString + ":" + tpe.toString
    case HOLAtom( x, args ) => x + "(" +
      ( if ( args.size > 1 ) args.head.toString + args.tail.foldLeft( "" )( ( s, a ) => s + ", " + a.toString )
      else args.foldLeft( "" )( ( s, a ) => s + a.toString ) ) + "): o"
    case HOLFunction( x, args, tpe ) => x + "(" +
      ( if ( args.size > 1 ) args.head.toString + args.tail.foldLeft( "" )( ( s, a ) => s + ", " + a.toString )
      else args.foldLeft( "" )( ( s, a ) => s + a.toString ) ) + "):" + tpe.toString
    case HOLAnd( x, y )      => "(" + x.toString + AndSymbol + y.toString + ")"
    case HOLEquation( x, y ) => "(" + x.toString + EqSymbol + y.toString + ")"
    case HOLOr( x, y )       => "(" + x.toString + OrSymbol + y.toString + ")"
    case HOLImp( x, y )      => "(" + x.toString + ImpSymbol + y.toString + ")"
    case HOLNeg( x )         => NegSymbol + x.toString
    case HOLExVar( x, f )    => ExistsSymbol + x.toString + "." + f.toString
    case HOLAllVar( x, f )   => ForallSymbol + x.toString + "." + f.toString
    case HOLAbs( v, exp )    => "(λ" + v.toString + "." + exp.toString + ")"
    case HOLApp( l, r )      => "(" + l.toString + ")" + "(" + r.toString + ")"
    case _                   => throw new Exception( "Unrecognized symbol." )
  }

  def arity: Int = this match {
    case HOLVar( _, _ ) | HOLConst( _, _ ) => 0
    case HOLNeg( _ ) | HOLAllVar( _, _ ) | HOLExVar( _, _ ) => 1
    case BinaryConnective( _, _ ) => 2
    case HOLAtom( _, args ) => args.length
    case HOLFunction( _, args, _ ) => args.length
    case HOLAbs( _, _ ) => 1
    case _ => throw new Exception( "Unhandled HOLExpression " + this + "." )
  }
  /**
   * Retrieves this expression's subexpression at a given position.
   *
   * @param pos The position to be retrieved.
   * @return The subexpression at pos.
   */
  def apply( pos: HOLPosition ): HOLExpression = get( pos ) match {
    case Some( f ) => f
    case None      => throw new Exception( "Position " + pos + " does not exist in expression " + this + "." )
  }

  /**
   * Retrieves this expression's subexpression at a given position, if there is one.
   *
   * @param pos The position to be retrieved.
   * @return If there is a subexpression at that position, return Some(that expression). Otherwise None.
   */
  def get( pos: HOLPosition ): Option[HOLExpression]

  /**
   * Tests whether this expression has a subexpression at a given position.
   *
   * @param pos The position to be tested.
   * @return Whether this(pos) is defined.
   */
  def isDefinedAt( pos: HOLPosition ): Boolean = toLambdaPositionOption( this )( pos ) match {
    case Some( _ ) => true
    case None      => false
  }

  /**
   * Finds all positions of a subexpression in this expression.
   *
   * @param exp The subexpression to be found.
   * @return A list containing all positions where exp occurs.
   */
  def find( exp: HOLExpression ): List[HOLPosition] = getPositions( this, _ == exp )

  def renameSymbols( map: SymbolMap ): HOLExpression = this match {
    case HOLVar( _, _ ) => this

    case HOLConst( name, exptype ) => map.get( name ) match {
      case Some( ( rArity, rName ) ) =>
        if ( Arity( exptype ) == rArity ) {
          HOLConst( StringSymbol( rName ), exptype )
        } else {
          this
        }
      case None => this
    }

    case HOLAtom( x: HOLVar, args )          => HOLAtom( x, args.map( _.renameSymbols( map ) ) )
    case HOLAtom( x: HOLConst, args )        => HOLAtom( x.renameSymbols( map ).asInstanceOf[HOLConst], args.map( _.renameSymbols( map ) ) )
    case HOLFunction( x: HOLVar, args, _ )   => HOLFunction( x, args.map( _.renameSymbols( map ) ) )
    case HOLFunction( x: HOLConst, args, _ ) => HOLFunction( x.renameSymbols( map ).asInstanceOf[HOLConst], args.map( _.renameSymbols( map ) ) )
    case HOLAnd( x, y )                      => HOLAnd( x.renameSymbols( map ), y.renameSymbols( map ) )
    case HOLEquation( x, y )                 => HOLEquation( x.renameSymbols( map ), y.renameSymbols( map ) )
    case HOLOr( x, y )                       => HOLOr( x.renameSymbols( map ), y.renameSymbols( map ) )
    case HOLImp( x, y )                      => HOLImp( x.renameSymbols( map ), y.renameSymbols( map ) )
    case HOLNeg( x )                         => HOLNeg( x.renameSymbols( map ) )
    // Variables are not renamed
    case HOLExVar( x, f )                    => HOLExVar( x, f.renameSymbols( map ) )
    case HOLAllVar( x, f )                   => HOLAllVar( x, f.renameSymbols( map ) )
  }
}
// Should this be here?
trait Formula extends LambdaExpression { require( exptype == To ) }

trait HOLFormula extends HOLExpression with Formula {
  override def renameSymbols( map: SymbolMap ) = super.renameSymbols( map ).asInstanceOf[HOLFormula]
}

case object HOLBottomC extends HOLConst( BottomSymbol, Type( "o" ) ) with HOLFormula
case object HOLTopC extends HOLConst( TopSymbol, Type( "o" ) ) with HOLFormula
case object HOLNegC extends HOLConst( NegSymbol, Type( "(o -> o)" ) )
case object HOLAndC extends HOLConst( AndSymbol, Type( "(o -> (o -> o))" ) )
case object HOLOrC extends HOLConst( OrSymbol, To -> ( To -> To ) )
case object HOLImpC extends HOLConst( ImpSymbol, Type( "(o -> (o -> o))" ) )
private[hol] class HOLEqC( e: TA ) extends HOLConst( EqSymbol, ->( e, ->( e, "o" ) ) )
object HOLEqC {
  private val es: mutable.Map[TA, HOLEqC] = mutable.Map[TA, HOLEqC]()

  def apply( e: TA ) = this.synchronized { es.getOrElseUpdate( e, new HOLEqC( e ) ) }
  def unapply( e: HOLExpression ) = e match {
    case c: HOLConst if c.sym == EqSymbol => Some( c.exptype )
    case _                                => None
  }
}

// We do in all of them additional casting into Formula as Formula is a static type and the only way to dynamically express it is via casting.
object HOLNeg {
  def apply( sub: HOLFormula ) = {
    val neg = sub.factory.createConnective( NegSymbol ).asInstanceOf[HOLConst]
    HOLApp( neg, sub ).asInstanceOf[HOLFormula]
  }
  def unapply( expression: HOLExpression ) = expression match {
    case HOLApp( HOLNegC, sub ) => Some( sub.asInstanceOf[HOLFormula] )
    case _                      => None
  }
}

object HOLAnd {
  def apply( fs: List[HOLFormula] ): HOLFormula = fs match {
    case Nil     => HOLTopC // No way to define from which layer this TopC comes from...
    case hd :: tl => fs.dropRight(1).foldRight( fs.last )( ( d, f ) => HOLAnd( d, f ) )

  }
  def apply( left: HOLFormula, right: HOLFormula ) = {
    val f_left = left.factory
    val f_right = right.factory
    val factory =
      if ( f_left == f_right )
        f_left
      else {
        // We are in a bit of a pickle here. Solve with a hack until discussed
        // in GAPT meeting.
        if ( f_left != HOLFactory )
          f_left
        else
          f_right
      }
    val and = factory.createConnective( AndSymbol ).asInstanceOf[HOLConst]
    HOLApp( HOLApp( and, left ), right ).asInstanceOf[HOLFormula]
  }
  def unapply( expression: HOLExpression ) = expression match {
    case HOLApp( HOLApp( HOLAndC, left ), right ) => Some( ( left.asInstanceOf[HOLFormula], right.asInstanceOf[HOLFormula] ) )
    case _                                        => None
  }
}

object HOLOr {
  def apply( fs: List[HOLFormula] ): HOLFormula = fs match {
    case Nil     => HOLBottomC // No way to define from which layer this BottomC comes from...
    case hd :: tl => fs.dropRight(1).foldRight( fs.last )( ( d, f ) => HOLOr( d, f ) )
  }
  def apply( left: HOLFormula, right: HOLFormula ): HOLFormula = {
    val f_left = left.factory
    val f_right = right.factory
    val factory =
      if ( f_left == f_right )
        f_left
      else {
        // We are in a bit of a pickle here. Solve with a hack until discussed
        // in GAPT meeting.
        if ( f_left != HOLFactory )
          f_left
        else
          f_right
      }

    val or = factory.createConnective( OrSymbol ).asInstanceOf[HOLConst]
    HOLApp( HOLApp( or, left ), right ).asInstanceOf[HOLFormula]
  }
  def unapply( expression: HOLExpression ) = expression match {
    case HOLApp( HOLApp( HOLOrC, left ), right ) => Some( ( left.asInstanceOf[HOLFormula], right.asInstanceOf[HOLFormula] ) )
    case _                                       => None
  }
}

object HOLImp {
  def apply( left: HOLFormula, right: HOLFormula ) = {
    val imp = left.factory.createConnective( ImpSymbol ).asInstanceOf[HOLConst]
    HOLApp( HOLApp( imp, left ), right ).asInstanceOf[HOLFormula]
  }
  def unapply( expression: HOLExpression ) = expression match {
    case HOLApp( HOLApp( HOLImpC, left ), right ) => Some( ( left.asInstanceOf[HOLFormula], right.asInstanceOf[HOLFormula] ) )
    case _                                        => None
  }
}

object HOLEquation {
  def apply( left: HOLExpression, right: HOLExpression ) = {
    require( left.exptype == right.exptype )
    val eq = left.factory.createConnective( EqSymbol, left.exptype ).asInstanceOf[HOLConst]
    HOLApp( HOLApp( eq, left ), right ).asInstanceOf[HOLFormula]
  }
  def unapply( expression: HOLExpression ) = expression match {
    case HOLApp( HOLApp( HOLEqC( _ ), left ), right ) => Some( left.asInstanceOf[HOLExpression], right.asInstanceOf[HOLExpression] )
    case _ => None
  }
}

object HOLFunction {
  def apply( head: HOLVar, args: List[HOLExpression] ): HOLExpression = apply_( head, args )
  def apply( head: HOLConst, args: List[HOLExpression] ): HOLExpression = apply_( head, args )

  private def apply_( head: HOLExpression, args: List[HOLExpression] ): HOLExpression = args match {
    case Nil     => head
    case t :: tl => apply_( HOLApp( head, t ), tl )
  }

  def unapply( expression: HOLExpression ) = expression match {
    case HOLApp( c: HOLConst, _ ) if isLogicalSymbol( c )              => None
    case HOLApp( HOLApp( c: HOLConst, _ ), _ ) if isLogicalSymbol( c ) => None
    case HOLApp( _, _ ) if ( expression.exptype != To ) =>
      unapply_( expression ) match {
        case Some( t ) =>
          Some( ( t._1, t._2, expression.exptype ) )
        case None => None
      }

    case _ => None
  }
  // Recursive unapply to get the head and args
  private def unapply_( e: HOLExpression ): Option[( HOLExpression, List[HOLExpression] )] = e match {
    case v: HOLVar   => Some( ( v, Nil ) )
    case c: HOLConst => Some( ( c, Nil ) )
    case HOLApp( e1, e2 ) =>
      unapply_( e1 ) match {
        case Some( ( x, y ) ) =>
          Some( ( x, y :+ e2 ) )
        case None =>
          None
      }

    case HOLAbs( _, _ ) =>
      None
  }
}

// HOL formulas of the form P(t_1,...,t_n)
object HOLAtom {
  def apply( head: HOLVar, args: List[HOLExpression] ): HOLFormula = apply_( head, args ).asInstanceOf[HOLFormula]
  def apply( head: HOLVar ): HOLFormula = head.asInstanceOf[HOLFormula]
  def apply( head: HOLConst, args: List[HOLExpression] ): HOLFormula = apply_( head, args ).asInstanceOf[HOLFormula]
  def apply( head: HOLConst ): HOLFormula = head.asInstanceOf[HOLFormula]

  private def apply_( head: HOLExpression, args: List[HOLExpression] ): HOLExpression = args match {
    case Nil     => head
    case t :: tl => apply_( HOLApp( head, t ), tl )
  }

  def unapply( expression: HOLExpression ) = expression match {
    case HOLApp( c: HOLConst, _ ) if isLogicalSymbol( c )              => None
    case HOLApp( HOLApp( c: HOLConst, _ ), _ ) if isLogicalSymbol( c ) => None
    case HOLApp( _, _ ) if ( expression.exptype == To ) => unapply_( expression ) match {
      /* the head constant must be a var or a constant, e.g. (\ x.Fx) s is not atomic, but its beta normal form
       * Fs is. */
      case p @ ( HOLVar( _, _ ), _ )   => Some( p )
      case p @ ( HOLConst( _, _ ), _ ) => Some( p )
      case _                           => None
    }
    case HOLConst( _, _ ) if ( expression.exptype == To ) => Some( ( expression, Nil ) )
    case HOLVar( _, _ ) if ( expression.exptype == To ) => Some( ( expression, Nil ) )
    case _ => None
  }
  // Recursive unapply to get the head and args
  private def unapply_( e: HOLExpression ): ( HOLExpression, List[HOLExpression] ) = e match {
    case v: HOLVar   => ( v, Nil )
    case c: HOLConst => ( c, Nil )
    case HOLApp( e1, e2 ) =>
      val t = unapply_( e1 )
      ( t._1, t._2 :+ e2 )
    case HOLAbs( x, t ) =>
      ( e, Nil )
  }
}

// TODO: Is it possible to simplify the quantifiers? There are too many objects for that...
class HOLExQ( e: TA ) extends HOLConst( ExistsSymbol, ->( e, "o" ) )
object HOLExQ {
  def apply( tp: TA ) = new HOLExQ( tp )
  def unapply( v: HOLConst ) = ( v, v.sym ) match {
    case ( HOLConst( _, t ), ExistsSymbol ) => Some( t )
    case _                                  => None
  }
}
class HOLAllQ( e: TA ) extends HOLConst( ForallSymbol, ->( e, "o" ) )
object HOLAllQ {
  def apply( tp: TA ) = new HOLAllQ( tp )
  def unapply( v: HOLConst ) = ( v, v.sym ) match {
    case ( HOLConst( _, t ), ForallSymbol ) => Some( t )
    case _                                  => None
  }
}

private object HOLEx {
  def apply( sub: HOLExpression ) = {
    val ex = sub.factory.createConnective( ExistsSymbol, sub.exptype ).asInstanceOf[HOLConst]
    HOLApp( ex, sub ).asInstanceOf[HOLFormula]
  }
  def unapply( expression: HOLExpression ) = expression match {
    case HOLApp( HOLExQ( t ), sub ) => Some( ( sub, t ) )
    case _                          => None
  }
}

private object HOLAll {
  def apply( sub: HOLExpression ) = {
    val all = sub.factory.createConnective( ForallSymbol, sub.exptype ).asInstanceOf[HOLConst]
    HOLApp( all, sub ).asInstanceOf[HOLFormula]
  }
  def unapply( expression: HOLExpression ) = expression match {
    case HOLApp( HOLAllQ( t ), sub ) => Some( ( sub, t ) )
    case _                           => None
  }
}

object HOLExVar {
  def apply( variable: HOLVar, sub: HOLFormula ) = HOLEx( HOLAbs( variable, sub ) )
  def unapply( expression: HOLExpression ) = expression match {
    case HOLEx( HOLAbs( variable, sub ), _ ) => Some( ( variable, sub.asInstanceOf[HOLFormula] ) )
    case _                                   => None
  }
}

object HOLAllVar {
  def apply( variable: HOLVar, sub: HOLFormula ) = HOLAll( HOLAbs( variable, sub ) )
  def unapply( expression: HOLExpression ) = expression match {
    case HOLAll( HOLAbs( variable, sub ), _ ) => Some( ( variable, sub.asInstanceOf[HOLFormula] ) )
    case _                                    => None
  }
}

/**
 * A block of existential quantifiers.
 *
 */
object HOLExVarBlock {

  /**
   *
   * @param vars A list of HOL variables v,,1,,, …, v,,n,,.
   * @param sub The formula F to be quantified over.
   * @return ∃v,,1,,…∃v,,n,,F
   */
  def apply( vars: List[HOLVar], sub: HOLFormula ): HOLFormula = vars match {
    case Nil     => sub
    case v :: vs => HOLExVar( v, HOLExVarBlock( vs, sub ) )
  }

  /**
   *
   * @param expression A HOLExpression
   * @return If expression begins with an ∃-block: a pair consisting of the variables of the block and the quantified subformula.
   */
  def unapply( expression: HOLExpression ) = expression match {
    case f: HOLFormula =>
      val ( vars, sub ) = unapplyHelper( f )
      if ( vars.nonEmpty ) Some( ( vars, sub ) )
      else None
    case _ => None
  }

  private def unapplyHelper( f: HOLFormula ): ( List[HOLVar], HOLFormula ) = f match {
    case HOLExVar( v, sub ) =>
      val ( subVars, subF ) = unapplyHelper( sub )
      ( v :: subVars, subF )
    case _ => ( Nil, f )
  }
}

/**
 * A block of universal quantifiers.
 *
 */
object HOLAllVarBlock {

  /**
   *
   * @param vars A list of HOL variables v,,1,,, …, v,,n,,.
   * @param sub The formula F to be quantified over.
   * @return ∀v,,1,,…∀v,,n,,F
   */
  def apply( vars: List[HOLVar], sub: HOLFormula ): HOLFormula = vars match {
    case Nil     => sub
    case v :: vs => HOLAllVar( v, HOLAllVarBlock( vs, sub ) )
  }

  /**
   *
   * @param expression A HOLExpression
   * @return If expression begins with an ∀-block: a pair consisting of the variables of the block and the quantified subformula.
   */
  def unapply( expression: HOLExpression ) = expression match {
    case f: HOLFormula =>
      val ( vars, sub ) = unapplyHelper( f )
      if ( vars.nonEmpty ) Some( ( vars, sub ) )
      else None
    case _ => None
  }

  private def unapplyHelper( f: HOLFormula ): ( List[HOLVar], HOLFormula ) = f match {
    case HOLAllVar( v, sub ) =>
      val ( subVars, subF ) = unapplyHelper( sub )
      ( v :: subVars, subF )
    case _ => ( Nil, f )
  }
}
