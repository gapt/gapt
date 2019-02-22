package gapt.expr.formula.fol

import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.formula.NonLogicalConstant
import gapt.expr.ty.Ty

private[expr] class FOLHead( ret: Ty ) {
  def apply( sym: String, arity: Int ): Const =
    Const( sym, FOLHeadType( ret, arity ) )
  def unapply( e: Expr ): Option[( String, Int )] = e match {
    case NonLogicalConstant( sym, FOLHeadType( `ret`, arity ), Nil ) => Some( ( sym, arity ) )
    case _ => None
  }
}

