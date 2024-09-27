package gapt.logic.hol

import gapt.expr.Abs
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Atom
import gapt.expr.formula.Bottom
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.Quant
import gapt.expr.formula.Top
import gapt.expr.formula.hol.instantiate
import gapt.expr.util.freeVariables
import gapt.logic.Polarity
import gapt.proofs.context.mutable.MutableContext

object skolemize {

  def apply(
      f: Formula,
      pol: Polarity = Polarity.InSuccedent,
      proofTheoretic: Boolean = false
  )(implicit ctx: MutableContext = MutableContext.guess(f)): Formula = {
    def go(f: Formula, pol: Polarity): Formula =
      f match {
        case Bottom() | Top() | Atom(_, _) => f
        case Neg(a)                        => -go(a, !pol)
        case And(a, b)                     => go(a, pol) & go(b, pol)
        case Or(a, b)                      => go(a, pol) | go(b, pol)
        case Imp(a, b)                     => go(a, !pol) --> go(b, pol)
        case Ex(x, a) if pol.inSuc         => Ex(x, go(a, pol))
        case All(x, a) if pol.inAnt        => All(x, go(a, pol))
        case Quant(_, _, _) =>
          val fvs = freeVariables(f).toVector
          val skC = ctx.addSkolemSym(Abs(fvs, f), reuse = !proofTheoretic)
          go(instantiate(f, skC(fvs)), pol)
      }
    go(f, pol)
  }

}
