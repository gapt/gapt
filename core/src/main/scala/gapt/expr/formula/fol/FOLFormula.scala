package gapt.expr.formula.fol

import gapt.expr.formula.And
import gapt.expr.formula.Formula
import gapt.expr.formula.Iff
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or

trait FOLFormula extends FOLPartialFormula with Formula with FOLExpression {
  private[expr] override val numberOfArguments = 0

  def &( that: FOLFormula ): FOLFormula = And( this, that )
  def |( that: FOLFormula ): FOLFormula = Or( this, that )
  override def unary_- : FOLFormula = Neg( this )
  def -->( that: FOLFormula ): FOLFormula = Imp( this, that )
  def <->( that: FOLFormula ): FOLFormula = Iff( this, that ).asInstanceOf[FOLFormula]
}
