package gapt.proofs.reduction

import gapt.expr.Const
import gapt.expr.stringInterpolationForExpressions
import gapt.expr.ty.TBase
import gapt.expr.ty.Ti
import gapt.proofs.SequentMatchers
import gapt.proofs.context.Context
import org.specs2.mutable._

class PredicateTranslationTest extends Specification with SequentMatchers {

  implicit var ctx: Context = Context.default

  val constants = Set( hoc"P : a > o", hoc"f : a > b", hoc"g : a > i" )
  val sorts = Set( TBase( "a" ), TBase( "b" ), Ti )

  sorts.foreach { ctx += _ }
  constants.foreach { ctx += _ }

  val predicateTranslation = PredicateTranslation( ctx )

  val pa = predicateTranslation.predicateForSort( TBase( "a" ) )
  val pb = predicateTranslation.predicateForSort( TBase( "b" ) )
  val pi = predicateTranslation.predicateForSort( TBase( "i" ) )

  "predicate translation" should {
    "generate fresh predicate constants" in {
      constants must not contain ( predicateTranslation.predicates.asInstanceOf[Set[Const]] )
    }

    "generate predicates for all base types except o" in {
      predicateTranslation.predicateForSort.keySet mustEqual sorts
    }

    "generate a non-emptiness axiom for each sort" in {
      predicateTranslation.nonEmptyAxioms mustEqual sorts.map {
        s => hof"${predicateTranslation.predicateForSort( s )}( ${Const( "nonempty_" + s.name, s )} )"
      }
    }

    "generate fresh non-emptiness Skolem constants" in {
      constants must not contain ( predicateTranslation.nonEmptyWitnesses )
    }

    "generate function axioms for all function constants" in {
      predicateTranslation.functionAxiom( hoc"f : a > b" ) mustEqual
        hof"(${pa}( x0 ) -> ${pb}( f(x0) ))"
      predicateTranslation.functionAxiom( hoc"g : a > i" ) mustEqual
        hof"(${pa}( x0 ) -> ${pi}( g(x0) ))"
      predicateTranslation.predicateAxioms.size mustEqual 2
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
