package gapt.expr.formula

import gapt.expr.Abs
import gapt.expr.App
import gapt.expr.Expr
import gapt.expr.Var
import gapt.expr.formula.constants.QuantifierC
import gapt.expr.formula.fol.FOLExpression
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.fol.FOLVar

class QuantifierHelper( val q: QuantifierC ) {
  def apply( v: Var, formula: Expr ): Formula =
    App( q( v.ty ), Abs( v, formula ) ).asInstanceOf[Formula]
  def apply( v: FOLVar, formula: FOLFormula ): FOLFormula =
    apply( v, formula.asInstanceOf[Expr] ).asInstanceOf[FOLFormula]

  def unapply( e: Expr ): Option[( Var, Formula )] = e match {
    // TODO: eta-expansion?
    case App( q( _ ), Abs( v, formula: Formula ) ) => Some( ( v, formula ) )
    case _                                         => None
  }

  def unapply( f: FOLFormula ): Option[( FOLVar, FOLFormula )] =
    unapply( f.asInstanceOf[FOLExpression] )
  def unapply( f: FOLExpression ): Option[( FOLVar, FOLFormula )] = unapply( f.asInstanceOf[Expr] ) match {
    case Some( ( v: FOLVar, formula: FOLFormula ) ) => Some( ( v, formula ) )
    case _ => None
  }

  object Block {
    def apply( vars: Seq[Var], formula: Expr ): Expr = vars match {
      case v +: vs => QuantifierHelper.this( v, apply( vs, formula ) )
      case Seq()   => formula
    }
    def apply( vars: Seq[Var], formula: Formula ): Formula =
      apply( vars, formula.asInstanceOf[Expr] ).asInstanceOf[Formula]
    def apply( vars: Seq[FOLVar], formula: FOLFormula ): FOLFormula =
      apply( vars, formula.asInstanceOf[Expr] ).asInstanceOf[FOLFormula]

    private object SingleQ {
      def unapply( e: Expr ): Option[( Var, Formula )] = QuantifierHelper.this.unapply( e )
    }
    def unapply( e: Expr ): Some[( List[Var], Expr )] = e match {
      case SingleQ( v, Block( vs, f ) ) => Some( ( v :: vs, f ) )
      case _                            => Some( ( List(), e ) )
    }
    def unapply( f: Formula ): Some[( List[Var], Formula )] =
      unapply( f.asInstanceOf[Expr] ).asInstanceOf[Some[( List[Var], Formula )]]
    def unapply( f: FOLFormula ): Some[( List[FOLVar], FOLFormula )] =
      unapply( f.asInstanceOf[Expr] ).asInstanceOf[Some[( List[FOLVar], FOLFormula )]]
  }
}
