package gapt.expr.subst

import gapt.expr.ClosedUnderFOLSub
import gapt.expr.formula.fol.FOLFormula
import gapt.expr.formula.fol.FOLTerm
import gapt.expr.formula.Atom

trait ExprSubstitutable6 extends ExprSubstitutable5 {
  implicit val FOLTermClosedUnderFOLSub: ClosedUnderFOLSub[FOLTerm] =
    (sub, x) => applySub(sub, x).asInstanceOf[FOLTerm]

  implicit val FOLFormulaClosedUnderFOLSub: ClosedUnderFOLSub[FOLFormula] =
    (sub, x) =>
      applySub(sub, x).asInstanceOf[FOLFormula]

  implicit val AtomClosedUnderFOLSub: ClosedUnderFOLSub[Atom] =
    (sub, x) => applySub(sub, x).asInstanceOf[Atom]
}
