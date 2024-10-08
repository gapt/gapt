package gapt.proofs.lk

import gapt.expr._
import gapt.expr.formula.All
import gapt.expr.formula.Bottom
import gapt.expr.formula.Eq
import gapt.expr.formula.Ex
import gapt.expr.formula.Formula
import gapt.expr.formula.Top
import gapt.expr.formula.fol.FOLAtom
import gapt.expr.formula.fol.FOLAtomConst
import gapt.expr.formula.fol.FOLVar
import gapt.proofs._
import gapt.proofs.lk.util.AtomicExpansion
import org.specs2.mutable._

class AtomicExpansionTest extends Specification {

  def test(f: Formula) = AtomicExpansion(f).endSequent must_== (f +: Sequent() :+ f)

  "atomic expansion" should {
    val Seq(p, q) = Seq("p", "q") map { FOLAtom(_) }
    val r = FOLAtomConst("r", 2)
    val Seq(x, y) = Seq("x", "y") map { FOLVar(_) }

    "atom" in { test(p) }
    "equality" in { test(Eq(x, x)) }
    "top" in { test(Top()) }
    "bottom" in { test(Bottom()) }
    "neg" in { test(-p) }
    "and" in { test(p & r(x, y)) }
    "or" in { test(p | q) }
    "imp" in { test(p --> q) }
    "all" in { test(All(x, r(x, y))) }
    "ex" in { test(Ex(x, r(x, y))) }
    "non-vnf" in { test(Ex(x, r(x, y) & All(x, Ex(y, r(x, y))))) }
  }

}
