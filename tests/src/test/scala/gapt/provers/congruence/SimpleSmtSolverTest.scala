package gapt.provers.congruence

import gapt.expr._
import gapt.expr.formula.fol.Numeral
import gapt.proofs._
import gapt.proofs.expansion.minimalExpansionSequent
import gapt.provers.escargot.Escargot
import org.specs2.mutable.Specification

class SimpleSmtSolverTest extends Specification {

  "qf_uf" in {
    "simple" in {
      SimpleSmtSolver.isValid(hof"(a=b | a=c) & P(c) & P(b) -> P(a)") must_== true
    }
  }

}
