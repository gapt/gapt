package gapt.expr.formula.hol

import gapt.expr.Const
import gapt.expr.ty.FunctionType
import gapt.expr.ty.To
import gapt.expr.ty.Ty

trait HOLAtomConst extends Const with HOLPartialAtom

object HOLAtomConst {
  def apply( name: String, argTypes: Ty* ): HOLAtomConst =
    Const( name, FunctionType( To, argTypes ) ).asInstanceOf[HOLAtomConst]

  def unapply( e: Const with HOLPartialAtom ): Option[( String, Seq[Ty] )] = e match {
    case Const( name, FunctionType( To, argTypes ), _ ) => Some( name -> argTypes )
  }
}