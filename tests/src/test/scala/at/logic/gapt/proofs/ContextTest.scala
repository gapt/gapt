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
