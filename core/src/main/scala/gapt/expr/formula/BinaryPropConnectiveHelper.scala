package gapt.expr.formula

import gapt.expr.App
import gapt.expr.Apps
import gapt.expr.Expr
import gapt.expr.formula.constants.MonomorphicLogicalC
import gapt.expr.formula.fol.FOLExpression
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.prop.PropFormula

class BinaryPropConnectiveHelper( val c: MonomorphicLogicalC ) {
  def apply( a: Expr, b: Expr ): Formula =
    Apps( c(), a, b ).asInstanceOf[Formula]
  def apply( a: FOLFormula, b: FOLFormula ): FOLFormula =
    apply( a, b.asInstanceOf[Expr] ).asInstanceOf[FOLFormula]
  def apply( a: PropFormula, b: PropFormula ): PropFormula =
    apply( a, b.asInstanceOf[Expr] ).asInstanceOf[PropFormula]

  def unapply( formula: Expr ): Option[( Formula, Formula )] = formula match {
    case App( App( c(), a: Formula ), b: Formula ) => Some( ( a, b ) )
    case _                                         => None
  }
  def unapply( formula: FOLFormula ): Option[( FOLFormula, FOLFormula )] =
    unapply( formula.asInstanceOf[FOLExpression] )
  def unapply( formula: FOLExpression ): Option[( FOLFormula, FOLFormula )] =
    unapply( formula.asInstanceOf[Expr] ) match {
      case Some( ( a: FOLFormula, b: FOLFormula ) ) => Some( ( a, b ) )
      case _                                        => None
    }
  def unapply( formula: PropFormula ): Option[( PropFormula, PropFormula )] =
    unapply( formula.asInstanceOf[Expr] ) match {
      case Some( ( a: PropFormula, b: PropFormula ) ) => Some( ( a, b ) )
      case _ => None
    }
}
