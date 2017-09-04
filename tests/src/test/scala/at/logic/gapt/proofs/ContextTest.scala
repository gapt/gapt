package at.logic.gapt.proofs

import at.logic.gapt.expr._
import org.specs2.mutable.Specification

class ContextTest extends Specification {
  import Context._

  "inductive type" in {
    "negative occurrences" in {
      default +
        InductiveType(
          "large",
          hoc"emptyset : large",
          hoc"comprehension : (large > o) > large" ) must throwAn[IllegalArgumentException]
    }

    "polymorphism" in {
      implicit var ctx = Context()
      ctx += Context.InductiveType(
        ty"list ?a",
        hoc"nil: list ?a",
        hoc"cons: ?a > list ?a > list ?a" )
      ctx += hof"xs + (x : ?a) = cons x xs"
      ctx += Context.Sort( "i" )
      ctx ++= Seq( hoc"0: i", hoc"1: i", hoc"2: i" )
      val e = le"nil + 3 + 2 + 1: list i"
      ctx.check( e )
      ctx.normalize( e ) must_== le"cons 1 (cons 2 (cons 3 nil))"
    }
  }

  "polymorphic definitions" in {
    implicit var ctx = Context()
    ctx += hof"const (f: ?a > ?b) = (!x!y f x = f y)"

    ctx += Context.Sort( "i" )
    ctx += hoc"0 : i"
    ctx += hof"g (x:i) = 0"

    import at.logic.gapt.proofs.gaptic._
    ctx.check( Lemma( hols":- const g" ) {
      unfold( "const", "g" ).in( "g" )
      decompose
      refl
    } )
    ok
  }

  "recursive functions" in {
    implicit var ctx = default
    ctx += InductiveType( "nat", hoc"0: nat", hoc"s: nat>nat" )
    ctx += PrimRecFun( hoc"'+': nat>nat>nat", "0 + x = x", "s(x) + y = s(x + y)" )
    ctx += hof"1 = s(0)"; ctx += hof"2 = s(1)"; ctx += hof"3 = s(2)"; ctx += hof"4 = s(3)"
    ctx.normalize( le"2 + 2" ) must_== ctx.normalize( le"4" )
  }

  "ite" in {
    implicit var ctx = default
    ctx += PrimRecFun( hoc"ite: o > ?a > ?a > ?a", "ite true a b = a", "ite false a b = b" )

    ctx += Ti; ctx += hoc"a: i"; ctx += hoc"b: i"
    ctx.whnf( le"ite true a b" ) must_== le"a"
    ctx.whnf( le"ite false a b" ) must_== le"b"

    // a version of negation that reduces definitionally
    ctx += PrimRecFun( hoc"neg : o > o", "neg true = false", "neg false = true" )
    ctx.whnf( le"ite (neg true) a b" ) must_== le"b"
    ctx.whnf( le"ite (neg false) a b" ) must_== le"a"
  }

  "propext" in {
    implicit var ctx = default
    import at.logic.gapt.proofs.gaptic._
    ctx check Lemma( Sequent() :+ ( "goal" -> hof"!p!q ((p <-> q) -> p = q)" ) ) {
      repeat( allR )
      induction( hov"p: o" ).onAll( induction( hov"q: o" ) )
      quasiprop.onAllSubGoals
    }
    ok
  }

}
