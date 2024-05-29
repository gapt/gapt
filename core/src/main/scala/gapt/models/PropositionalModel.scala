package gapt.models

import gapt.expr._
import gapt.expr.formula.And
import gapt.expr.formula.Atom
import gapt.expr.formula.Bottom
import gapt.expr.formula.Formula
import gapt.expr.formula.Imp
import gapt.expr.formula.Neg
import gapt.expr.formula.Or
import gapt.expr.formula.Top
import gapt.logic.Polarity
import gapt.proofs.{HOLClause, Sequent}

/** Propositional interpretation */
case class PropositionalModel(assignment: Map[Atom, Boolean]) {
  def trueAtoms: Iterable[Atom] = for ((a, p) <- assignment if p) yield a

  def toCube: HOLClause = Sequent {
    for ((a, v) <- assignment)
      yield (a, if (v) Polarity.InAntecedent else Polarity.InSuccedent)
  }

  /** Truth value of the formula in this model */
  def apply(f: Formula): Boolean = f match {
    case And(f1, f2) => apply(f1) && apply(f2)
    case Or(f1, f2)  => apply(f1) || apply(f2)
    case Imp(f1, f2) => !apply(f1) || apply(f2)
    case Neg(f1)     => !apply(f1)
    case Bottom()    => false
    case Top()       => true
    case atom: Atom  => assignment.getOrElse(atom, false)
  }

  override def toString: String = assignment.toSeq.map { case (atom, value) => s"$atom -> $value" }.sorted.mkString(sys.props("line.separator"))
}

object PropositionalModel {
  def apply(model: Iterable[(Atom, Boolean)]): PropositionalModel =
    PropositionalModel(Map() ++ model)
}
