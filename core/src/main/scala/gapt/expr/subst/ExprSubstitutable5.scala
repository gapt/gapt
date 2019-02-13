package gapt.expr.subst

import gapt.expr.Atom
import gapt.expr.FOLAtom

trait ExprSubstitutable5 extends ExprSubstitutable4 {
  implicit val FOLAtomSubstitutable: Substitutable[Substitution, FOLAtom, Atom] =
    ( sub, x ) => applySub( sub, x ).asInstanceOf[Atom]
}
