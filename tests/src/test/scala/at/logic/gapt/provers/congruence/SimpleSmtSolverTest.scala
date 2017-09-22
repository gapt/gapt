package at.logic.gapt.provers.congruence

import at.logic.gapt.expr._
import at.logic.gapt.expr.fol.Numeral
import at.logic.gapt.proofs._
import at.logic.gapt.proofs.expansion.minimalExpansionSequent
import at.logic.gapt.provers.escargot.Escargot
import org.specs2.mutable.Specification

class SimpleSmtSolverTest extends Specification {

  "qf_uf" in {
    "simple" in {
      SimpleSmtSolver.isValid( hof"(a=b | a=c) & P(c) & P(b) -> P(a)" ) must_== true
    }
  }

  "ac" in {
    val solver = new SimpleSmtSolver( acTheory( FOLFunctionConst( "*", 2 ), commutative = true ).step )

    "ac 1" in {
      solver.isValid( hof"a * b = c & c * c = 1 -> b*c*a = 1" ) must_== true
    }

    "ac 2" in {
      solver.isValid( hof"(a * b = c | c = c * c & b * a = 1) & c * c = 1 -> b*c*a = 1" ) must_== true
    }
  }

  "factorial minimization" in {
    val n = Numeral( 2 )
    val seq =
      hof"""
           !x!y!z x*(y*z) = (x*y)*z ->
           !x!y x*y = y*x ->
           !x x*s(0) = x ->
           !x s(0)*x = x ->
           f(0) = s(0) & !x f(s(x)) = s(x)*f(x) ->
           !y g(0,y) = y & !x!y g(s(x),y) = g(x, s(x)*y) ->
           f($n) = g($n, s(0))
         """
    val Some( expansion ) = Escargot.getExpansionProof( seq )

    val acTh = acTheory( FOLFunctionConst( "*", 2 ), commutative = true )
    val uTh = unitTheory( FOLFunctionConst( "*", 2 ), le"s(0)" )
    val solver = new SimpleSmtSolver( cc => acTh.step( uTh.step( cc ) ) )
    val Some( minimized ) = minimalExpansionSequent( expansion, solver )
    ok
  }

}
