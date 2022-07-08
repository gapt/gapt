package gapt.logic

import gapt.expr._
import gapt.expr.formula.And
import gapt.expr.formula.Eq
import gapt.expr.formula.Neg
import gapt.proofs.context.update.InductiveType
import gapt.utils.unorderedPairsOf
import org.specs2.mutable.Specification

class AxiomsTest extends Specification {

  "injectivity axioms" should {
    "not be generated for nullary constructors" in {
      val natType = InductiveType( "Nat", hoc"0:Nat", hoc"S:Nat>Nat" )
      injectivityAxioms( natType ).size mustEqual 1
    }
    "cover all non-nullary constructors" in {
      val natType = InductiveType( "Nat", hoc"0:Nat", hoc"S:Nat>Nat" )
      injectivityAxioms( natType ) must contain( hof"!x !y (#c(S:Nat>Nat)(x) = S(y) -> x = y)" )
    }
    "have the form c(x₁,...,xₙ) = c(y₁,...,yₙ) → x₁ = y₁ ∧ ... ∧ xₙ = yₙ" in {
      injectivityAxiom( hoc"c:i>i" ) mustEqual hof"!x !y (c(x) = c(y) -> x = y)"
    }
  }

  "disjointness axioms" should {
    "be generated for all unordered pairs of constructors" in {
      val natType = InductiveType( "Nat", hoc"0:Nat", hoc"S:Nat>Nat" )
      disjointnessAxioms( natType ) mustEqual Iterable( hof"!x #c(0:Nat) != #c(S:Nat>Nat)(x)" )
    }
    "have the form " in {
      disjointnessAxiom( hoc"c:i", hoc"d:i" ) mustEqual hof"c != d"
      disjointnessAxiom( hoc"c:i", hoc"d:i>i" ) mustEqual hof"!x c != d(x)"
      disjointnessAxiom( hoc"c:i>i", hoc"d:i>i" ) mustEqual hof"!x !y c(x) != d(y)"
    }
  }

  "distinctness formula" should {
    "be top for zero arguments" in { AllDistinct() must_== hof"⊤" }
    "be top for one argument" in { AllDistinct() must_== hof"⊤" }
    "contain a disequality for each unordered  pair of the arguments" in {
      val terms = List( hov"x : i", hov"y: i", hov"z : i" )
      val And.nAry( conjuncts ) = AllDistinct( terms: _* )
      conjuncts.map { case Neg( Eq( t1, t2 ) ) => ( t1, t2 ) } must_== unorderedPairsOf( terms )
    }
  }
}
