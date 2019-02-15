package gapt.expr.subst

import gapt.expr.ClosedUnderFOLSub
import gapt.expr.formula.FOLAtom

trait ExprSubstitutable7 extends ExprSubstitutable6 {
  implicit val FOLAtomClosedUnderFOLSub: ClosedUnderFOLSub[FOLAtom] =
    ( sub, x ) => applySub( sub, x ).asInstanceOf[FOLAtom]
}
