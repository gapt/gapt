package gapt.proofs.reduction

import gapt.expr.Const
import gapt.expr.stringInterpolationForExpressions
import gapt.expr.ty.TBase
import gapt.expr.ty.Ti
import gapt.proofs.SequentMatchers
import org.specs2.mutable._

class PredicateTranslationTest extends Specification with SequentMatchers {

  val cs = Set( hoc"P : a > o", hoc"f : a > b", hoc"g : a > i" )

  val sorts = Set( TBase( "a" ), TBase( "b" ), Ti )

  val predicateTranslation = PredicateTranslation( cs )

  val pa = predicateTranslation.predicateForSort( TBase( "a" ) )
  val pb = predicateTranslation.predicateForSort( TBase( "b" ) )
  val pi = predicateTranslation.predicateForSort( TBase( "i" ) )

  "predicate translation" should {
    "generate fresh predicate constants" in {
      cs must not contain ( predicateTranslation.predicates.asInstanceOf[Set[Const]] )
    }

    "generate predicates for all base types except o" in {
      predicateTranslation.predicateForSort.keySet mustEqual sorts
    }

    "generate a non-emptiness axiom for each sort" in {
      predicateTranslation.nonEmptyAxioms mustEqual sorts.map {
        s => hof"${predicateTranslation.predicateForSort( s )}( ${"nonempty_" + s.name} )"
      }
    }

    "generate fresh non-emptiness Skolem constants" in {
      cs must not contain ( predicateTranslation.nonEmptyWitnesses )
    }

    "generate predicate axioms for all function constants" in {
      predicateTranslation.predicateAxioms mustEqual Set(
        hof"(${pa}( x0 ) -> ${pb}( f(x0) ))",
        hof"(${pa}( x0 ) -> ${pi}( g(x0) ))" )
    }

    "guard" in {
      "existential quantifiers" in {
        predicateTranslation.guard( hof"?x P( x : a )" ) mustEqual hof"?x (${pa}(x) & P( x ))"
      }
      "universal quantifiers" in {
        predicateTranslation.guard( hof"!x P( x : a )" ) mustEqual hof"!x (${pa}(x) -> P( x ))"
      }
    }

    "unguard" in {
      "existential quantifiers" in {
        val f = hof"?x (${pa}(x) & P( x : a ))"
        predicateTranslation.unguard( f ) mustEqual hof"?x P( x : a )"
      }
      "universal quantifiers" in {
        val f = hof"!x (${pa}(x) -> P( x : a ))"
        predicateTranslation.unguard( f ) mustEqual hof"!x P( x : a )"
      }
    }
  }
}
