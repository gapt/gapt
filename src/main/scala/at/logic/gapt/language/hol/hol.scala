/*
 * hol.scala
 */

package at.logic.gapt.language.hol

import at.logic.gapt.expr._

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
  def apply( vars: List[Var], sub: HOLFormula ): HOLFormula = vars match {
    case Nil     => sub
    case v :: vs => Ex( v, ExBlock( vs, sub ) )
  }

  /**
   *
   * @param expression A LambdaExpression
   * @return If expression begins with an ∃-block: a pair consisting of the variables of the block and the quantified subformula.
   */
  def unapply( expression: LambdaExpression ) = expression match {
    case f: HOLFormula =>
      val ( vars, sub ) = unapplyHelper( f )
      if ( vars.nonEmpty ) Some( ( vars, sub ) )
      else None
    case _ => None
  }

  private def unapplyHelper( f: HOLFormula ): ( List[Var], HOLFormula ) = f match {
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
  def apply( vars: List[Var], sub: HOLFormula ): HOLFormula = vars match {
    case Nil     => sub
    case v :: vs => All( v, AllBlock( vs, sub ) )
  }

  /**
   *
   * @param expression A LambdaExpression
   * @return If expression begins with an ∀-block: a pair consisting of the variables of the block and the quantified subformula.
   */
  def unapply( expression: LambdaExpression ) = expression match {
    case f: HOLFormula =>
      val ( vars, sub ) = unapplyHelper( f )
      if ( vars.nonEmpty ) Some( ( vars, sub ) )
      else None
    case _ => None
  }

  private def unapplyHelper( f: HOLFormula ): ( List[Var], HOLFormula ) = f match {
    case All( v, sub ) =>
      val ( subVars, subF ) = unapplyHelper( sub )
      ( v :: subVars, subF )
    case _ => ( Nil, f )
  }
}
