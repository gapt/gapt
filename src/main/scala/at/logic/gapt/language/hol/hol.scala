/*
 * hol.scala
 */

package at.logic.gapt.language.hol

import at.logic.gapt.language.hol.HOLPosition._
import at.logic.gapt.expr.symbols.StringSymbol
import at.logic.gapt.expr.types._
import at.logic.gapt.expr._
import at.logic.gapt.expr.{ LambdaExpression }

import scala.collection.mutable

//  def arity: Int = this match {
//    case Var( _, _ ) | Const( _, _ ) => 0
//    case Neg( _ ) | All( _, _ ) | Ex( _, _ ) => 1
//    case BinaryConnective( _, _ ) => 2
//    case HOLAtom( _, args ) => args.length
//    case HOLFunction( _, args, _ ) => args.length
//    case Abs( _, _ ) => 1
//    case _ => throw new Exception( "Unhandled LambdaExpression " + this + "." )
//  }

/**
 * A block of existential quantifiers.
 *
 */
object ExBlock {

  /**
   *
   * @param vars A list of HOL variables v,,1,,, …, v,,n,,.
   * @param sub The formula F to be quantified over.
   * @return ∃v,,1,,…∃v,,n,,F
   */
  def apply( vars: List[Var], sub: Formula ): Formula = vars match {
    case Nil     => sub
    case v :: vs => Ex( v, ExBlock( vs, sub ) )
  }

  /**
   *
   * @param expression A LambdaExpression
   * @return If expression begins with an ∃-block: a pair consisting of the variables of the block and the quantified subformula.
   */
  def unapply( expression: LambdaExpression ) = expression match {
    case f: Formula =>
      val ( vars, sub ) = unapplyHelper( f )
      if ( vars.nonEmpty ) Some( ( vars, sub ) )
      else None
    case _ => None
  }

  private def unapplyHelper( f: Formula ): ( List[Var], Formula ) = f match {
    case Ex( v, sub ) =>
      val ( subVars, subF ) = unapplyHelper( sub )
      ( v :: subVars, subF )
    case _ => ( Nil, f )
  }
}

/**
 * A block of universal quantifiers.
 *
 */
object AllBlock {

  /**
   *
   * @param vars A list of HOL variables v,,1,,, …, v,,n,,.
   * @param sub The formula F to be quantified over.
   * @return ∀v,,1,,…∀v,,n,,F
   */
  def apply( vars: List[Var], sub: Formula ): Formula = vars match {
    case Nil     => sub
    case v :: vs => All( v, AllBlock( vs, sub ) )
  }

  /**
   *
   * @param expression A LambdaExpression
   * @return If expression begins with an ∀-block: a pair consisting of the variables of the block and the quantified subformula.
   */
  def unapply( expression: LambdaExpression ) = expression match {
    case f: Formula =>
      val ( vars, sub ) = unapplyHelper( f )
      if ( vars.nonEmpty ) Some( ( vars, sub ) )
      else None
    case _ => None
  }

  private def unapplyHelper( f: Formula ): ( List[Var], Formula ) = f match {
    case All( v, sub ) =>
      val ( subVars, subF ) = unapplyHelper( sub )
      ( v :: subVars, subF )
    case _ => ( Nil, f )
  }
}
