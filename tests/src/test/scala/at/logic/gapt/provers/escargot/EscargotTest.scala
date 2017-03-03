package at.logic.gapt.provers.escargot

import at.logic.gapt.examples.{ BussTautology, CountingEquivalence, Permutations, PigeonHolePrinciple }
import at.logic.gapt.expr.fol.{ naive, thresholds }
import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.existentialClosure
import at.logic.gapt.formats.babel.BabelParser
import at.logic.gapt.proofs.Sequent
import org.specs2.mutable._

class EscargotTest extends Specification {
  import BabelParser.parseFormula

  def parse( formulas: String* ) = existentialClosure { ( formulas map parseFormula ) ++: Sequent() }
  def test( formulas: String* ) = Escargot getResolutionProof parse( formulas: _* )

  "simple" in { test( "P(x)", "-P(c)" ) must beSome }

  "linear" in { test( "p(0)", "p(x) -> p(s(x))", "-p(s(s(s(s(0)))))" ) must beSome }

  "multiple preds" in {
    test( "p(c,y)", "p(x,f(y)) & p(x,g(y)) -> p(f(x),y)",
      "q(d,y)", "q(x,f(y)) & q(x,f(f(y))) -> q(g(x),y)",
      "-p(f(f(c)),d) | -q(g(g(d)),c)" ) must beSome
  }

  "refl" in { test( "x != x" ) must beSome }
  "unifying refl" in { test( "x != c" ) must beSome }
  "flip" in { test( "a = b", "b != a" ) must beSome }
  "double" in { test( "f(x) = g(g(x))", "g(g(g(x))) = x", "g(c) != f(f(c))" ) must beSome }
  "cond eq" in { test( "p(c)", "p(x) -> p(f(x))", "p(x) -> f(x) = g(x)", "f(f(c)) != g(g(c))" ) must beSome }

  "buss taut" in { Escargot getResolutionProof BussTautology( 4 ) must beSome }
  "php" in { Escargot getResolutionProof PigeonHolePrinciple( 3, 2 ) must beSome }
  "perms" in { Escargot getResolutionProof Permutations( 5 ) must beSome }

  "los" in {
    test(
      "p(x,y) & p(y,z) -> p(x,z)",
      "q(x,y) & q(y,z) -> q(x,z)", "q(x,y) -> q(y,x)",
      "p(x,y) | q(x,y)",
      "-p(a,b)", "-q(c,d)"
    ) must beSome
  }

  "davis putnam" in { test( "-(?x ?y !z ((f(x,y) -> f(y,z) & f(z,z)) & (f(x,y) & g(x,y) -> g(x,z) & g(z,z))))" ) must beSome }

  "large cnf" in { Escargot getResolutionProof CountingEquivalence( 5 ) must beSome }

  "drinker" in { Escargot getResolutionProof hof"?x (p(x) -> !y p(y))" must beSome }
  "barber" in { Escargot getResolutionProof hof"-?x !y (shaves(x,y) <-> -shaves(y,y))" must beSome }

  "two plus two" in { test( "x + 0 = x", "x + s(y) = s(x+y)", "s(s(0)) + s(s(0)) != s(s(s(s(0))))" ) must beSome }
  "two times two" in { test( "x + 0 = x", "x + s(y) = s(x+y)", "x * 0 = 0", "x*s(y) = (x*y) + x", "s(s(0)) * s(s(0)) != s(s(s(s(0))))" ) must beSome }

  "exponential" in { test( "p(0,y)", "p(x,f(y)) & p(x,g(y)) -> p(s(x),y)", "p(x,c) -> q(x)", "-q(s(s(s(0))))" ) must beSome }

  "skk eq i" in { test( "f(a,x) = x", "f(f(f(b,x),y),z) = f(f(x,z), f(y,z))", "f(f(c,x),y) = x", "f(f(f(b,c),c),x) != f(a,x)" ) must beSome }

  "assoc inst" in { test( "f(f(x,y),z) = f(x,f(y,z))", "f(f(a2,f(a1,a1)),a2) != f(a2,f(a1,f(a1,a2)))" ) must beSome }
  "assoc inst from e" in { test( "f(f(x,y),z) = f(x,f(y,z))", "f(f(a2,f(a1,a1)),f(a2,f(a1,a1))) != f(a2,f(f(a1,a1),f(a2,f(a1,a1))))" ) must beSome }

  "replay" in { test( "divide(u,v)=0 -> less_equal(u,v)", "divide(a,b)=0", "-less_equal(a,b)" ) must beSome }
  "replay from spass" in {
    test(
      "less_equal(u,v) -> divide(u,v)=Zero",
      "less_equal(u,v) -> divide(divide(u,w),divide(v,w))=Zero",
      "less_equal(U,V) & less_equal(W,U) & divide(divide(W,V),Zero)!=Zero"
    ) must beSome
  }

  "demodulator vs unification" in { test( "f(u) != 0", "0 = f(a)" ) must beSome }

  "ac" in {
    test(
      "x+(y+z) = (x+y)+z",
      "x+y = y+x",
      "(a+(b+c))+(d+e) != (c+(d+(a+e)))+b"
    ) must beSome
  }

  "sat ac" in {
    test(
      "x+(y+z) = (x+y)+z",
      "x+y = y+x",
      "(a+(b+c))+(d+e) != (b+(d+(a+e)))+b"
    ) must beNone
  }

  "two factorials" in {
    test(
      "x*(y*z) = (x*y)*z",
      "x*y = y*x",
      "f1(0) = s(0) & f1(s(x)) = s(x) * f1(x)",
      "f2(0) = s(0) & f2(s(x)) = f2(x) * s(x)",
      "f1(s(s(s(s(0))))) != f2(s(s(s(s(0)))))"
    ) must beSome
  }

  "group inverses" in {
    test(
      "x*(y*z) = (x*y)*z",
      "1*x = x",
      "i(x)*x = 1",
      "a*i(a) != 1"
    ) must beSome
  }

  "primitive support for lambdas" in { test( "!y (^x f(x,y)) = g(y) & r(g(c)) & -r(^x f(x,c))" ) must beSome }
}
