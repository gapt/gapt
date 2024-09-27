package gapt.expr.formula.constants

import gapt.expr.Const
import gapt.expr.Expr
import gapt.expr.ty.->:
import gapt.expr.ty.To
import gapt.expr.ty.Ty

object EqC extends LogicalC("=") {
  def apply(ty: Ty) = Const(name, ty ->: ty ->: To, ty :: Nil)

  def unapply(e: Expr): Option[Ty] = e match {
    case Const(n, t, ps) => unapply((n, t, ps))
    case _               => None
  }
  def unapply(p: (String, Ty, List[Ty])): Option[Ty] =
    p match {
      case (`name`, ty_ ->: ty__ ->: To, ty :: Nil) if ty == ty_ && ty_ == ty__ => Some(ty)
      case _                                                                    => None
    }
}
