/*
 * fol.scala
 */

package at.logic.gapt.language.fol

import at.logic.gapt.language.lambda.FactoryA
import at.logic.gapt.language.hol.{ HOLEqC => HOLEqC, _ }
import at.logic.gapt.language.lambda.symbols._
import at.logic.gapt.language.lambda.types._
import at.logic.gapt.language.hol.logicSymbols._

/**
 * The following is a note about the construction of this trait. Right now FOLExpression refers to both valid FOL terms
 * and formulas and components of such valid terms and formulas, so for example, the head symbol of an atom is also a
 * fol expression although it has a complex type.
 * @author ?
 * @version ?
 */

trait FOLExpression extends HOLExpression {
  /**
   * This function takes a FOL construction and converts it to a string version. The String version is made
   * by replacing the code construction for logic symbols by string   versions in the file language/hol/logicSymbols.scala.
   * Terms are also handled by the this function.
   *
   * @param  this  The method has no parameters other then the object which is to be written as a string
   *
   * @throws Exception This occurs when an unknown subformula is found when parsing the FOL construction
   *
   * @return A String which contains the defined symbols in language/hol/logicSymbols.scala.
   *
   */
  override def toString: String = this match {
    case FOLVar( x )   => x.toString
    case FOLConst( x ) => x.toString
    case FOLAtom( x, args ) => x + "(" +
      ( if ( args.size > 1 ) args.head.toString + args.tail.foldLeft( "" )( ( s, a ) => s + ", " + a.toString )
      else args.foldLeft( "" )( ( s, a ) => s + a.toString ) ) + ")"
    case FOLFunction( x, args ) => x + "(" +
      ( if ( args.size > 1 ) args.head.toString + args.tail.foldLeft( "" )( ( s, a ) => s + ", " + a.toString )
      else args.foldLeft( "" )( ( s, a ) => s + a.toString ) ) + ")"
    case FOLAnd( x, y )    => "(" + x.toString + AndSymbol + y.toString + ")"
    case FOLOr( x, y )     => "(" + x.toString + OrSymbol + y.toString + ")"
    case FOLImp( x, y )    => "(" + x.toString + ImpSymbol + y.toString + ")"
    case FOLNeg( x )       => NegSymbol + x.toString
    case FOLExVar( x, f )  => ExistsSymbol + x.toString + "." + f.toString
    case FOLAllVar( x, f ) => ForallSymbol + x.toString + "." + f.toString
    case FOLAbs( v, exp )  => "(λ" + v.toString + "." + exp.toString + ")"
    case FOLApp( l, r )    => "(" + l.toString + ")" + "(" + r.toString + ")"
    case _ =>
      val r = super.toString
      throw new Exception( "toString: expression is not FOL: " + r )
  }

  override def renameSymbols( map: SymbolMap ): FOLExpression = this match {

    case FOLVar( _ ) => this

    case FOLConst( name ) => map.get( name ) match {
      case Some( ( rArity, rName ) ) =>
        if ( Arity( this.exptype ) == rArity ) {
          FOLConst( StringSymbol( rName ) )
        } else {
          this
        }
      case None => this
    }

    case FOLAtom( x, args ) => map.get( x.toString ) match {
      case Some( ( rArity, rName ) ) =>
        if ( args.length == rArity ) {
          FOLAtom( StringSymbol( rName ), args.map( _.renameSymbols( map ).asInstanceOf[FOLTerm] ) )
        } else {
          FOLAtom( x, args.map( _.renameSymbols( map ).asInstanceOf[FOLTerm] ) )
        }
      case None => FOLAtom( x, args.map( _.renameSymbols( map ).asInstanceOf[FOLTerm] ) )
    }

    case FOLFunction( x, args ) => map.get( x.toString ) match {
      case Some( ( rarity, rname ) ) =>
        if ( args.length == rarity ) {
          FOLFunction( StringSymbol( rname ), args.map( _.renameSymbols( map ).asInstanceOf[FOLTerm] ) )
        } else {
          FOLFunction( x, args.map( _.renameSymbols( map ).asInstanceOf[FOLTerm] ) )
        }
      case None => FOLFunction( x, args.map( _.renameSymbols( map ).asInstanceOf[FOLTerm] ) )
    }
    case FOLAnd( x, y )      => FOLAnd( x.renameSymbols( map ), y.renameSymbols( map ) )
    case FOLEquation( x, y ) => FOLEquation( x.renameSymbols( map ).asInstanceOf[FOLTerm], y.renameSymbols( map ).asInstanceOf[FOLTerm] )
    case FOLOr( x, y )       => FOLOr( x.renameSymbols( map ), y.renameSymbols( map ) )
    case FOLImp( x, y )      => FOLImp( x.renameSymbols( map ), y.renameSymbols( map ) )
    case FOLNeg( x )         => FOLNeg( x.renameSymbols( map ) )
    // Variables are not renamed
    case FOLExVar( x, f )    => FOLExVar( x, f.renameSymbols( map ) )
    case FOLAllVar( x, f )   => FOLAllVar( x, f.renameSymbols( map ) )
  }

  override def factory: FactoryA = FOLFactory
}

trait FOLFormula extends FOLExpression with HOLFormula {
  override def renameSymbols( map: SymbolMap ) = super.renameSymbols( map ).asInstanceOf[FOLFormula]
}

trait FOLTerm extends FOLExpression { require( exptype == Ti ) }

case object FOLTopC extends FOLLambdaConst( TopSymbol, To ) with FOLFormula
case object FOLBottomC extends FOLLambdaConst( BottomSymbol, To ) with FOLFormula
case object FOLNegC extends FOLLambdaConst( NegSymbol, To -> To )
case object FOLAndC extends FOLLambdaConst( AndSymbol, To -> ( To -> To ) )
case object FOLOrC extends FOLLambdaConst( OrSymbol, To -> ( To -> To ) )
case object FOLImpC extends FOLLambdaConst( ImpSymbol, To -> ( To -> To ) )
case object FOLEqC extends FOLLambdaConst( EqSymbol, Ti -> ( Ti -> To ) )

object FOLEquation {
  def apply( left: FOLTerm, right: FOLTerm ) = {
    val eq = left.factory.createConnective( EqSymbol ).asInstanceOf[FOLExpression]
    FOLApp( FOLApp( eq, left ), right ).asInstanceOf[FOLFormula]
  }
  def unapply( expression: FOLExpression ) = expression match {
    case FOLApp( FOLApp( FOLEqC, left ), right ) => Some( left.asInstanceOf[FOLTerm], right.asInstanceOf[FOLTerm] )
    case _                                       => None
  }
}

// FOL atom of the form P(t_1,...,t_n)
object FOLAtom {
  def apply( head: String, args: List[FOLTerm] ): FOLFormula = {
    val tp = FunctionType( To, args.map( a => a.exptype ) )
    val f = FOLLambdaConst( head, tp )
    apply_( f, args ).asInstanceOf[FOLFormula]
  }
  def apply( head: String ): FOLFormula = FOLLambdaConst( head, To ).asInstanceOf[FOLFormula]
  def apply( head: SymbolA, args: List[FOLTerm] ): FOLFormula = {
    val tp = FunctionType( To, args.map( a => a.exptype ) )
    val f = FOLLambdaConst( head, tp )
    apply_( f, args ).asInstanceOf[FOLFormula]
  }
  def apply( head: SymbolA ): FOLFormula = FOLLambdaConst( head, To ).asInstanceOf[FOLFormula]

  private def apply_( head: FOLExpression, args: List[FOLTerm] ): FOLExpression = args match {
    case Nil     => head
    case t :: tl => apply_( FOLApp( head, t ), tl )
  }

  def unapply( expression: FOLExpression ) = expression match {
    case FOLApp( c: FOLLambdaConst, _ ) if isLogicalSymbol( c ) => None
    case FOLApp( FOLApp( c: FOLLambdaConst, _ ), _ ) if isLogicalSymbol( c ) => None
    case FOLApp( _, _ ) if ( expression.exptype == To ) => Some( unapply_( expression ) )
    case c: FOLLambdaConst if ( c.exptype == To ) => Some( ( c.sym, Nil ) )
    case v: FOLVar if ( v.exptype == To ) => Some( ( v.sym, Nil ) )
    case _ => None
  }
  // Recursive unapply to get the head and args
  private def unapply_( e: FOLExpression ): ( SymbolA, List[FOLTerm] ) = e match {
    //case v: FOLVar => (v.sym, Nil)
    case c: FOLLambdaConst => ( c.sym, Nil )
    case FOLApp( e1, e2 ) =>
      val t = unapply_( e1 )
      ( t._1, t._2 :+ e2.asInstanceOf[FOLTerm] )
  }
}

// FOL function of the form f(t_1,...,t_n)
object FOLFunction {

  def apply( head: String, args: List[FOLTerm] ): FOLTerm = {
    val tp = FunctionType( Ti, args.map( a => a.exptype ) )
    val f = FOLLambdaConst( head, tp )
    apply_( f, args ).asInstanceOf[FOLTerm]
  }
  def apply( head: SymbolA, args: List[FOLTerm] ): FOLTerm = {
    val tp = FunctionType( Ti, args.map( a => a.exptype ) )
    val f = FOLLambdaConst( head, tp )
    apply_( f, args ).asInstanceOf[FOLTerm]
  }

  private def apply_( head: FOLExpression, args: List[FOLTerm] ): FOLExpression = args match {
    case Nil     => head
    case t :: tl => apply_( FOLApp( head, t ), tl )
  }

  def unapply( expression: FOLExpression ) = expression match {
    case FOLApp( c: FOLLambdaConst, _ ) if isLogicalSymbol( c )              => None
    case FOLApp( FOLApp( c: FOLLambdaConst, _ ), _ ) if isLogicalSymbol( c ) => None
    case FOLApp( _, _ ) if ( expression.exptype != To ) =>
      val t = unapply_( expression )
      Some( ( t._1, t._2 ) )
    case _ => None
  }
  // Recursive unapply to get the head and args
  private def unapply_( e: FOLExpression ): ( SymbolA, List[FOLTerm] ) = e match {
    case c: FOLLambdaConst => ( c.sym, Nil )
    case FOLApp( e1, e2 ) =>
      val t = unapply_( e1 )
      ( t._1, t._2 :+ e2.asInstanceOf[FOLTerm] )
  }
}

object FOLNeg {
  def apply( sub: FOLFormula ) = {
    val neg = sub.factory.createConnective( NegSymbol ).asInstanceOf[FOLExpression]
    FOLApp( neg, sub ).asInstanceOf[FOLFormula]
  }
  def unapply( expression: FOLExpression ) = expression match {
    case FOLApp( FOLNegC, sub ) => Some( ( sub.asInstanceOf[FOLFormula] ) )
    case _                      => None
  }
}

object FOLAnd {
  def apply( fs: List[FOLFormula] ): FOLFormula = fs match {
    case Nil     => FOLTopC
    case f :: fs => fs.foldLeft( f )( ( d, f ) => FOLAnd( d, f ) )
  }
  def apply( left: FOLFormula, right: FOLFormula ) = {
    val and = left.factory.createConnective( AndSymbol ).asInstanceOf[FOLExpression]
    FOLApp( FOLApp( and, left ), right ).asInstanceOf[FOLFormula]
  }
  def unapply( expression: FOLExpression ) = expression match {
    case FOLApp( FOLApp( FOLAndC, left ), right ) => Some( ( left.asInstanceOf[FOLFormula], right.asInstanceOf[FOLFormula] ) )
    case _                                        => None
  }
}

object FOLOr {
  def apply( fs: List[FOLFormula] ): FOLFormula = fs match {
    case Nil     => FOLBottomC
    case f :: fs => fs.foldLeft( f )( ( d, f ) => FOLOr( d, f ) )
  }
  def apply( left: FOLFormula, right: FOLFormula ) = {
    val or = left.factory.createConnective( OrSymbol ).asInstanceOf[FOLExpression]
    FOLApp( FOLApp( or, left ), right ).asInstanceOf[FOLFormula]
  }
  def unapply( expression: FOLExpression ) = expression match {
    case FOLApp( FOLApp( FOLOrC, left ), right ) => Some( ( left.asInstanceOf[FOLFormula], right.asInstanceOf[FOLFormula] ) )
    case _                                       => None
  }
}

object FOLImp {
  def apply( left: FOLFormula, right: FOLFormula ) = {
    val imp = left.factory.createConnective( ImpSymbol ).asInstanceOf[FOLExpression]
    FOLApp( FOLApp( imp, left ), right ).asInstanceOf[FOLFormula]
  }
  def unapply( expression: FOLExpression ) = expression match {
    case FOLApp( FOLApp( FOLImpC, left ), right ) => Some( ( left.asInstanceOf[FOLFormula], right.asInstanceOf[FOLFormula] ) )
    case _                                        => None
  }
}

private class FOLExQ extends FOLLambdaConst( ExistsSymbol, ->( ->( Ti, To ), To ) )
private object FOLExQ {
  def apply() = new FOLExQ
  def unapply( v: FOLLambdaConst ) = v match {
    case vo: FOLExQ => Some()
    case _          => None
  }
}

private class FOLAllQ extends FOLLambdaConst( ForallSymbol, ->( ->( Ti, To ), To ) )
private object FOLAllQ {
  def apply() = new FOLAllQ
  def unapply( v: FOLLambdaConst ) = v match {
    case vo: FOLAllQ => Some()
    case _           => None
  }
}

private object FOLEx {
  def apply( sub: FOLExpression ) = {
    val ex = sub.factory.createConnective( ExistsSymbol ).asInstanceOf[FOLExpression]
    FOLApp( ex, sub ).asInstanceOf[FOLFormula]
  }
  def unapply( expression: FOLExpression ) = expression match {
    case FOLApp( c: FOLExQ, sub ) => Some( sub )
    case _                        => None
  }
}

private object FOLAll {
  def apply( sub: FOLExpression ) = {
    val all = sub.factory.createConnective( ForallSymbol ).asInstanceOf[FOLExpression]
    FOLApp( all, sub ).asInstanceOf[FOLFormula]
  }
  def unapply( expression: FOLExpression ) = expression match {
    case FOLApp( c: FOLAllQ, sub ) => Some( sub )
    case _                         => None
  }
}

object FOLExVar {
  def apply( variable: FOLVar, sub: FOLFormula ) = FOLEx( FOLAbs( variable, sub ) )
  def unapply( expression: FOLExpression ) = expression match {
    case FOLEx( FOLAbs( variable: FOLVar, sub: FOLFormula ) ) => Some( ( variable, sub ) )
    case _ => None
  }
}

object FOLAllVar {
  def apply( variable: FOLVar, sub: FOLFormula ) = FOLAll( FOLAbs( variable, sub ) )

  def apply( vars: List[FOLVar], sub: FOLFormula ): FOLFormula = vars match {
    case Nil       => sub
    case v :: tail => apply( v, apply( tail, sub ) )
  }

  def unapply( expression: FOLExpression ) = expression match {
    case FOLAll( FOLAbs( variable: FOLVar, sub: FOLFormula ) ) => Some( ( variable, sub ) )
    case _ => None
  }
}

/**
 * A block of existential quantifiers.
 *
 */
object FOLExVarBlock {

  /**
   *
   * @param vars A list of FOL variables v,,1,,, …, v,,n,,.
   * @param sub The formula F to be quantified over.
   * @return ∃v,,1,,…∃v,,n,,F
   */
  def apply( vars: List[FOLVar], sub: FOLFormula ): FOLFormula = vars match {
    case Nil     => sub
    case v :: vs => FOLExVar( v, FOLExVarBlock( vs, sub ) )
  }

  /**
   *
   * @param expression A FOLExpression
   * @return If expression begins with an ∃-block: a pair consisting of the variables of the block and the quantified subformula.
   */
  def unapply( expression: FOLExpression ) = expression match {
    case f: FOLFormula =>
      val ( vars, sub ) = unapplyHelper( f )
      if ( vars.nonEmpty ) Some( ( vars, sub ) )
      else None
    case _ => None
  }

  private def unapplyHelper( f: FOLFormula ): ( List[FOLVar], FOLFormula ) = f match {
    case FOLExVar( v, sub ) =>
      val ( subVars, subF ) = unapplyHelper( sub )
      ( v :: subVars, subF )
    case _ => ( Nil, f )
  }
}

/**
 * A block of universal quantifiers.
 *
 */
object FOLAllVarBlock {

  /**
   *
   * @param vars A list of FOL variables v,,1,,, …, v,,n,,.
   * @param sub The formula F to be quantified over.
   * @return ∀v,,1,,…∀v,,n,,F
   */
  def apply( vars: List[FOLVar], sub: FOLFormula ): FOLFormula = vars match {
    case Nil     => sub
    case v :: vs => FOLAllVar( v, FOLAllVarBlock( vs, sub ) )
  }

  /**
   *
   * @param expression A FOLExpression
   * @return If expression begins with an ∀-block: a pair consisting of the variables of the block and the quantified subformula.
   */
  def unapply( expression: FOLExpression ) = expression match {
    case f: FOLFormula =>
      val ( vars, sub ) = unapplyHelper( f )
      if ( vars.nonEmpty ) Some( ( vars, sub ) )
      else None
    case _ => None
  }

  private def unapplyHelper( f: FOLFormula ): ( List[FOLVar], FOLFormula ) = f match {
    case FOLAllVar( v, sub ) =>
      val ( subVars, subF ) = unapplyHelper( sub )
      ( v :: subVars, subF )
    case _ => ( Nil, f )
  }
}

