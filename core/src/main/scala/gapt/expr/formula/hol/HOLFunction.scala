package gapt.expr.formula.hol

import gapt.expr.Apps
import gapt.expr.Expr
import gapt.expr.Var
import gapt.expr.formula.NonLogicalConstant
import gapt.expr.ty.To

object HOLFunction {
  def apply(head: Expr, args: List[Expr]): Expr = {
    val res = Apps(head, args)
    require(res.ty != To)
    res
  }
  def unapply(e: Expr): Option[(Expr, List[Expr])] = e match {
    case Apps(head @ (NonLogicalConstant(_, _, _) | Var(_, _)), args) if e.ty != To => Some(head, args)
    case _                                                                          => None
  }
}
