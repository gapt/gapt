package gapt.expr.formula

import gapt.expr.Apps
import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.Var
import gapt.expr.formula.hol.HOLPartialAtom
import gapt.expr.ty.FunctionType
import gapt.expr.ty.To

trait Atom extends Formula with HOLPartialAtom {
  private[expr] override def numberOfArguments: Int = 0
}

object Atom {
  def apply(head: String, args: Expr*)(implicit dummyImplicit: DummyImplicit): Atom =
    apply(head, args)
  def apply(head: String, args: Seq[Expr]): Atom =
    Apps(Const(head, FunctionType(To, args.map(_.ty))), args).asInstanceOf[Atom]

  def apply(head: Expr, args: Expr*): Atom =
    apply(head, args toList)
  def apply(head: Expr, args: List[Expr]): Atom =
    Apps(head, args).asInstanceOf[Atom]

  def unapply(e: Atom): Option[(Expr, List[Expr])] = e match {
    case Apps(head @ (Const(_, _, _) | Var(_, _)), args) if e.ty == To => Some(head, args)
    case _                                                             => None
  }
}
