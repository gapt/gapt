package gapt.expr.formula

import gapt.expr.Var

object Quant {
  def apply(x: Var, sub: Formula, pol: Boolean): Formula =
    if (pol) All(x, sub) else Ex(x, sub)

  def unapply(f: Formula): Option[(Var, Formula, Boolean)] =
    f match {
      case All(v, g) => Some((v, g, true))
      case Ex(v, g)  => Some((v, g, false))
      case _         => None
    }
}
