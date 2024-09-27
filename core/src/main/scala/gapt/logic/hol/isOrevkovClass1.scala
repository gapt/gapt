package gapt.logic.hol

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
import gapt.proofs.HOLSequent
import gapt.proofs.RichFormulaSequent

/**
 * Checks whether a sequent is in (a minor extension of) Orevkov's class 1.
 *
 * This is a Glivenko class, i.e., whenever this function returns true for a first-order formula,
 * then that formula is provable in intuitionistic logic iff it is provable in classical logic.
 */
object isOrevkovClass1 {
  private def pos: Formula => Boolean = {
    case Top() | Bottom() | _: Atom =>
      true
    case Ex(_, f)  => pos(f)
    case And(f, g) => pos(f) && pos(g)
    case Or(f, g)  => pos(f) && pos(g)
    case _         => false
  }

  private def neg: Formula => Boolean = {
    case Top() | Bottom() | _: Atom =>
      true
    case Ex(_, f)  => neg(f)
    case All(_, f) => neg(f)
    case And(f, g) => neg(f) && neg(g)
    case Or(f, g)  => neg(f) && neg(g)
    case Imp(f, g) => pos(f) && neg(g)
    case Neg(f)    => pos(f)
    case _         => false
  }

  private def fml: Formula => Boolean = {
    case Imp(f, g) => neg(f) && fml(g)
    case Neg(f)    => neg(f)
    case And(f, g) => fml(f) && fml(g)
    case All(_, f) => fml(f)
    case f         => pos(f)
  }

  def apply(formula: Formula): Boolean = fml(formula)
  def apply(sequent: HOLSequent): Boolean = apply(sequent.toImplication)
}
