/*
 * fol.scala
 */

package at.logic.gapt.language.fol

import at.logic.gapt.expr._

/**
 * A block of existential quantifiers.
 *
 */
object ExBlock {

  /**
   *
   * @param vars A list of FOL variables v,,1,,, …, v,,n,,.
   * @param sub The formula F to be quantified over.
   * @return ∃v,,1,,…∃v,,n,,F
   */
  def apply( vars: List[FOLVar], sub: FOLFormula ): FOLFormula = vars match {
    case Nil     => sub
    case v :: vs => Ex( v, ExBlock( vs, sub ) )
  }

  /**
   *
   * @param expression A FOLExpression
   * @return If expression begins with an ∃-block: a pair consisting of the variables of the block and the quantified subformula.
   */
  def unapply( expression: FOLFormula ) = expression match {
    case f: FOLFormula =>
      val ( vars, sub ) = unapplyHelper( f )
      if ( vars.nonEmpty ) Some( ( vars, sub ) )
      else None
    case _ => None
  }

  private def unapplyHelper( f: FOLFormula ): ( List[FOLVar], FOLFormula ) = f match {
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
   * @param vars A list of FOL variables v,,1,,, …, v,,n,,.
   * @param sub The formula F to be quantified over.
   * @return ∀v,,1,,…∀v,,n,,F
   */
  def apply( vars: List[FOLVar], sub: FOLFormula ): FOLFormula = vars match {
    case Nil     => sub
    case v :: vs => All( v, AllBlock( vs, sub ) )
  }

  /**
   *
   * @param expression A FOLExpression
   * @return If expression begins with an ∀-block: a pair consisting of the variables of the block and the quantified subformula.
   */
  def unapply( expression: FOLFormula ) = expression match {
    case f: FOLFormula =>
      val ( vars, sub ) = unapplyHelper( f )
      if ( vars.nonEmpty ) Some( ( vars, sub ) )
      else None
    case _ => None
  }

  private def unapplyHelper( f: FOLFormula ): ( List[FOLVar], FOLFormula ) = f match {
    case All( v, sub ) =>
      val ( subVars, subF ) = unapplyHelper( sub )
      ( v :: subVars, subF )
    case _ => ( Nil, f )
  }
}

