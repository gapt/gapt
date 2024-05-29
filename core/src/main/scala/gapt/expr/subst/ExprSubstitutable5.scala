package gapt.expr.subst

import gapt.expr.formula.Atom
import gapt.expr.formula.fol.FOLAtom

trait ExprSubstitutable5 extends ExprSubstitutable4 {
  implicit val FOLAtomSubstitutable: Substitutable[Substitution, FOLAtom, Atom] =
    (sub, x) => applySub(sub, x).asInstanceOf[Atom]
}
