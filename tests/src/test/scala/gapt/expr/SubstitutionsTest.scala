/*
 * SubstitutionsTest.scala
 */

package gapt.expr

import org.specs2.mutable._

import BetaReduction._
import org.specs2.execute.Success

class SubstitutionsTest extends Specification {

  "Substitutions" should {
    "NOT compose the substitution {f(y)/x} and {g(y)/x}" in {
      val x = Var( "x", Ti );
      val y = Var( "y", Ti );
      val f = Var( "f", Ti ->: Ti )
      val g = Var( "g", Ti ->: Ti )
      val e1 = App( f, y )
      val e2 = App( g, y )
      val sub1 = Substitution( x, e1 )
      val sub2 = Substitution( x, e2 )
      val sub = sub1 compose sub2
      sub must beEqualTo( sub2 )
    }
    "substitute correctly when Substitution is applied (1)" in {
      val v = Var( "v", Ti );
      val x = Var( "x", Ti );
      val f = Var( "f", Ti ->: Ti )
      val e = App( f, x )
      val sigma = Substitution( v, e )
      ( e ) must beEqualTo( sigma( v ) )
    }
    "substitute correctly when Substitution is applied (2)" in {
      val v = Var( "v", Ti ); val x = Var( "x", Ti ); val f = Var( "f", Ti ->: Ti )
      val e = App( f, x )
      val sigma = Substitution( v, e )
      val expression = App( f, v )
      ( App( f, App( f, x ) ) ) must beEqualTo( sigma( expression ) )
    }
    "substitute correctly when Substitution is applied (3)" in {
      val v = Var( "v", Ti ); val x = Var( "x", Ti ); val f = Var( "f", Ti ->: Ti )
      val y = Var( "y", Ti )
      val e = App( f, x )
      val sigma = Substitution( v, e )
      val expression = Abs( y, App( f, v ) )
      ( Abs( y, App( f, App( f, x ) ) ) ) must beEqualTo( sigma( expression ) )
    }
    "substitute correctly when SingleSubstitution is applied, renaming bound variables (1)" in {
      val v = Var( "v", Ti );
      val x = Var( "x", Ti );
      val f = Var( "f", Ti ->: Ti )
      val e = App( f, x )
      val sigma = Substitution( v, e )
      val exp1 = Abs( x, App( f, v ) )
      val exp2 = sigma( exp1 )
      val exp3 = Abs( x, App( f, App( f, x ) ) )
      ( exp2 ) must be_!=( exp3 )
    }
    "substitute correctly when SingleSubstitution is applied, renaming bound variables (2)" in {
      val v = Var( "v", Ti ); val x = Var( "x", Ti ); val f = Var( "f", Ti ->: Ti )
      val e = App( f, x )
      val sigma = Substitution( v, e )
      val exp1 = Abs( f, App( f, v ) )
      val exp2 = sigma( exp1 )
      val exp3 = Abs( f, App( f, App( f, x ) ) )
      ( exp2 ) must be_!=( exp3 )
    }
    "substitute correctly in presence of variant variables" in {
      val x = Var( "x", Ti )
      val xprime = rename( x, List( x ) )
      val y = Var( "y", Ti )
      val z = Var( "z", Ti )
      val f = Var( "f", Ti ->: Ti ->: Ti ->: Ti )
      val M = Abs( x, App( f, List( x, y, z ) ) )
      val sigma = Substitution( List( ( y, x ), ( z, xprime ) ) )
      val w = Var( "w", Ti )
      val Msigma = sigma( M )
      val Msigma_correct = Abs( w, App( f, List( w, x, xprime ) ) )

      ( Msigma ) must beEqualTo( Msigma_correct )
    }
    "substitute and normalize correctly when Substitution is applied" in {
      val x = Var( "X", Ti ->: To )
      val f = Var( "f", ( Ti ->: To ) ->: Ti )
      val xfx = App( x, App( f, x ) )

      val z = Var( "z", Ti )
      val p = Var( "P", Ti ->: To )
      val Pz = App( p, z )
      val t = Abs( z, Pz )

      val sigma = Substitution( x, t )

      betaNormalize( sigma.apply( xfx ) ) must beEqualTo( App( p, App( f, t ) ) )
    }
    "substitute correctly when Substitution is applied" in {
      val v = Var( "v", Ti )
      val x = Var( "x", Ti )
      val f = Var( "f", Ti ->: Ti )
      val e = App( f, v )
      val sigma1 = Substitution( v, x )
      ( sigma1( e ) ) must beEqualTo( App( f, x ) )
    }
    "not substitute for bound variables in (\\x.fx)x with sub {x |-> gy}" in {
      val term1 = App( Abs( Var( "x", Ti ), App( Var( "f", Ti ->: Ti ), Var( "x", Ti ) ) ), Var( "x", Ti ) )
      val sub = Substitution( Var( "x", Ti ), App( Var( "g", Ti ->: Ti ), Var( "y", Ti ) ) )
      val term2 = App( Abs( Var( "x", Ti ), App( Var( "f", Ti ->: Ti ), Var( "x", Ti ) ) ), App( Var( "g", Ti ->: Ti ), Var( "y", Ti ) ) )
      ( sub( term1 ) ) must beEqualTo( term2 )
    }
    "not substitute for bound variables in (\\x.fx)x with sub {x |-> (\\x.fx)c}" in {
      "- 1" in {
        val term1 = App( Abs( Var( "x", Ti ), App( Var( "f", Ti ->: Ti ), Var( "x", Ti ) ) ), Var( "x", Ti ) )
        val sub = Substitution( Var( "x", Ti ), App( Abs( Var( "x", Ti ), App( Var( "f", Ti ->: Ti ), Var( "x", Ti ) ) ), Var( "c", Ti ) ) )
        val term2 = App( Abs( Var( "x", Ti ), App( Var( "f", Ti ->: Ti ), Var( "x", Ti ) ) ), App( Abs( Var( "x", Ti ), App( Var( "f", Ti ->: Ti ), Var( "x", Ti ) ) ), Var( "c", Ti ) ) )
        ( sub( term1 ) ) must beEqualTo( term2 )
      }
      "- 2" in {
        val term1 = App( Abs( Var( "x", Ti ), App( Var( "f", Ti ->: Ti ), Var( "x", Ti ) ) ), Var( "x", Ti ) )
        val sub = Substitution( Var( "x", Ti ), App( Abs( Var( "x", Ti ), App( Var( "f", Ti ->: Ti ), Var( "x", Ti ) ) ), Var( "c", Ti ) ) )
        val term2 = App( Abs( Var( "z", Ti ), App( Var( "f", Ti ->: Ti ), Var( "z", Ti ) ) ), App( Abs( Var( "w", Ti ), App( Var( "f", Ti ->: Ti ), Var( "w", Ti ) ) ), Var( "c", Ti ) ) )
        ( sub( term1 ) ) must beEqualTo( term2 )
      }
    }
    "substitute correctly when substituting a term with bound variables into the scope of other bound variables" in {
      val term1 = Abs( Var( "x", Ti ), App( Var( "F", Ti ->: Ti ), Var( "x", Ti ) ) )
      val sub = Substitution( Var( "F", Ti ->: Ti ), Abs( Var( "x", Ti ), App( Var( "f", Ti ->: Ti ), Var( "x", Ti ) ) ) )
      val term2 = Abs( Var( "x", Ti ), App( Abs( Var( "x", Ti ), App( Var( "f", Ti ->: Ti ), Var( "x", Ti ) ) ), Var( "x", Ti ) ) )
      ( sub( term1 ) ) must beEqualTo( term2 )
    }
    "correctly apply a substitution when a bound variable appears both in its domain and its range" in {
      val x = Var( "x", Ti )
      val y = Var( "y", Ti )
      val z = Var( "z", Ti )
      val u = Var( "u", Ti )
      val f = Var( "f", Ti ->: Ti ->: Ti )
      val term1 = Abs( y, App( App( f, x ), y ) )
      val sub = Substitution( List( ( x, y ), ( y, z ) ) )
      val term2 = Abs( u, App( App( f, y ), u ) )
      ( sub( term1 ) ) must beEqualTo( term2 )
    }
    "work correctly on subterms of abs (i.e. the variables which were bound there are no longer bound)" in {
      val term1 = Abs( Var( "F", Ti ->: Ti ), Abs( Var( "x", Ti ), App( Var( "F", Ti ->: Ti ), Var( "x", Ti ) ) ) )
      val sub = Substitution( term1.variable, Abs( Var( "x", Ti ), App( Var( "f", Ti ->: Ti ), Var( "x", Ti ) ) ) )
      val term2 = Abs( Var( "x", Ti ), App( Abs( Var( "x", Ti ), App( Var( "f", Ti ->: Ti ), Var( "x", Ti ) ) ), Var( "x", Ti ) ) )
      ( sub( term1.term ) ) must beEqualTo( term2 )
    }
    "not substitute terms with different types" in {
      val x = Var( "x", Ti )
      val f = Var( "f", Ti ->: Ti )
      val e = App( f, x )
      val g = Var( "g", Ti )
      Substitution( f -> g ) must throwAn[IllegalArgumentException]
    }
    "not substitute variables with different types" in {
      val x = Var( "x", Ti ->: Ti )
      val c = Var( "c", Ti )
      Substitution( x -> c ) must throwAn[IllegalArgumentException]
    }

    "issue 383" in {
      val p = Const( "p", Ti ->: To )
      val x = Var( "x", Ti )
      val x0 = rename( x, Set( x ) )

      val formula = All( x, p( x ) )
      Substitution( x0 -> x )( formula ) must_== formula
    }

    "yet another renaming bug" in {
      val p = FOLFunctionConst( "p", 2 )
      val x = Var( "x", Ti )
      val x0 = rename( x, Set( x ) )
      val y = Var( "y", Ti )

      val formula = Abs( x, p( x, x0 ) )
      Substitution( y -> x )( formula ) must_== formula
    }
  }

  "injective renaming" in {
    Substitution( hov"x" -> le"c" ).isInjectiveRenaming must_== false
  }

  "injectivity test" in {
    Substitution( hov"x" -> le"y", hov"z" -> le"e" ).isInjectiveOnDomain must_== false
    Substitution( hov"x" -> le"f (g z) (g z)", hov"y" -> le"g z" ).isInjectiveOnDomain must_== false
    Substitution( hov"x" -> le"f (g z) (h z)", hov"y" -> le"g z" ).isInjectiveOnDomain must_== true
    Substitution( hov"x" -> le"g y" ).isInjectiveOnDomain must_== true
    Substitution( hov"x" -> le"y" ).isInjective( Set( hov"x" ) ) must_== true
    Substitution( hov"x" -> le"f z", hov"y" -> le"z" ).isInjective( Set( hov"x" ) ) must_== true
    Substitution( hov"x" -> le"y" ).isInjective( Set( hov"x", hov"y" ) ) must_== false
  }

  "issue 682" in {
    val f1 = hof"P(#v(x:i)) -> ∀(x:?a) P(#v(x:i))"
    val subst = Substitution( Map(), Map( TVar( "a" ) -> ty"i" ) )
    val wrong = hof"P(x) -> ∀x P(x)"
    val right = hof"P(x) -> ∀y P(x)"
    subst( f1 ) must_!= wrong
    subst( f1 ) must_== right
  }
}
