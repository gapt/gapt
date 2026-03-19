package gapt.proofs.expansion

import gapt.expr.Const
import gapt.expr.formula.Atom
import gapt.expr.formula.Ex
import gapt.expr.formula.fol.FOLVar
import gapt.expr.ty.Ti
import gapt.expr.ty.To
import gapt.logic.Polarity
import gapt.proofs.context.mutable.MutableContext
import gapt.proofs.context.update.Update
import gapt.utils.Maybe
import org.specs2.mutable.Specification

class ExpansionTreeTest extends Specification {
  "check() should throw if expansion tree contains symbol not in context even though shallow formula checks" in {
    given context: MutableContext = MutableContext.default()
    val x = FOLVar("x")
    val A = Const("A", Ti ->: To)
    val zero = Const("0", Ti)
    val shallow = Ex(x, Atom(A, x))
    context += Ti
    context += A
    context.check(shallow) must not(throwAn[IllegalArgumentException])
    ETWeakQuantifier(
      shallow,
      Map(zero -> ETAtom(Atom(A, zero), Polarity.InSuccedent))
    ).check()(using context) must throwAn[IllegalArgumentException]
  }

  "check should not throw if context contains symbol from expansion" in {
    given context: MutableContext = MutableContext.default()
    val x = FOLVar("x")
    val A = Const("A", Ti ->: To)
    val zero = Const("0", Ti)
    val shallow = Ex(x, Atom(A, x))
    context += Ti
    context += A
    context += zero
    context.check(shallow) must not(throwAn[IllegalArgumentException])
    ETWeakQuantifier(
      Ex(x, Atom(A, x)),
      Map(zero -> ETAtom(Atom(A, zero), Polarity.InSuccedent))
    ).check()(using context) must not(throwAn[IllegalArgumentException])
  }
}
