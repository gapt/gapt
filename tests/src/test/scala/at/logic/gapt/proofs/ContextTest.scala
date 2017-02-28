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
          hoc"comprehension : (large > o) > large"
        ) must throwAn[IllegalArgumentException]
    }

    "polymorphism" in {
      implicit var ctx = Context()
      ctx += Context.InductiveType(
        ty"list ?a",
        hoc"nil: list ?a",
        hoc"cons: ?a > list ?a > list ?a"
      )
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

}
