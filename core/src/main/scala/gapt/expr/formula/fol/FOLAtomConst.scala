package gapt.expr.formula.fol

import gapt.expr.App
import gapt.expr.Expr
import gapt.expr.formula.constants.EqC
import gapt.expr.formula.hol.HOLAtomConst
import gapt.expr.ty.Ti
import gapt.expr.ty.To

trait FOLAtomConst extends HOLAtomConst with FOLPartialAtom {
  def apply( that: FOLTerm* )( implicit dummyImplicit: DummyImplicit ): FOLAtom = App( this, that ).asInstanceOf[FOLAtom]
}

object FOLAtomConst extends FOLHead( To ) {
  override def apply( sym: String, arity: Int ): FOLAtomConst =
    if ( sym == "=" && arity == 2 ) EqC( Ti ).asInstanceOf[FOLAtomConst] else
      super.apply( sym, arity ).asInstanceOf[FOLAtomConst]
  override def unapply( e: Expr ): Option[( String, Int )] = e match {
    case EqC( Ti ) => Some( "=", 2 )
    case _         => super.unapply( e )
  }
}