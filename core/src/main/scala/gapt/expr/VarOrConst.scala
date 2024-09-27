package gapt.expr

import gapt.expr.ty.Ty

trait VarOrConst extends Expr {
  def name: String
}

/**
 * Matches constants and variables, but nothing else.
 */
object VarOrConst {
  def unapply(e: VarOrConst): Some[(String, Ty, List[Ty])] =
    e match {
      case Const(n, t, p) => Some(n, t, p)
      case Var(n, t)      => Some(n, t, Nil)
    }
}
