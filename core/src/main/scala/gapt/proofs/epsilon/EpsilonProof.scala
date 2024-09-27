package gapt.proofs.epsilon

import gapt.expr.formula.hol.instantiate
import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.And
import gapt.expr.formula.Atom
import gapt.expr.formula.Bottom
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.Top
import gapt.expr.subst.Substitution
import gapt.proofs.HOLSequent

case class CriticalFormula(existential: Formula, term: Expr) {
  val Ex(bound, qfFormula) = existential: @unchecked
  val eps = Epsilon(bound, qfFormula)

  val formula = instantiate(existential, term) --> instantiate(existential, eps)
}

case class EpsilonProof(
    criticalFormula: Seq[CriticalFormula],
    shallow: HOLSequent
) {
  val deep = criticalFormula.map(_.formula) ++: shallow.map(epsilonize(_))

  override def toString = deep.toString
}

object epsilonize {
  def apply(f: Formula): Formula = f match {
    case Top() | Bottom() | Atom(_, _) => f
    case Neg(a)                        => Neg(apply(a))
    case And(a, b)                     => And(apply(a), apply(b))
    case Or(a, b)                      => Or(apply(a), apply(b))
    case Imp(a, b)                     => Imp(apply(a), apply(b))
    case Ex(x, a) =>
      val a_ = apply(a)
      Substitution(x -> Epsilon(x, a_))(a_)
    case All(x, a) =>
      val a_ = apply(a)
      Substitution(x -> Epsilon(x, -a_))(a_)
  }
}
