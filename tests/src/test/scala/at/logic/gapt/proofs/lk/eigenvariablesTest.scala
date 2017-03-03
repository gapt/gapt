package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.{ Context, Sequent }
import org.specs2.mutable._

class eigenvariablesTest extends Specification {

  implicit var ctx = Context()
  ctx += Context.InductiveType( "nat", hoc"0: nat", hoc"s:nat>nat" )
  ctx += hoc"'+': nat>nat>nat"

  val plus_axioms = Seq(
    "ap1" -> hof"∀y 0+y = y",
    "ap2" -> hof"∀x∀y s(x)+y = s(x+y)"
  )

  val proof = Lemma( plus_axioms ++: Sequent() :+
    ( "goal" -> hof"!x x + (y + z) = (x + y) + z" ) ) {
    allR
    induction( hov"x:nat" )
    rewrite.many ltr "ap1" in "goal"
    refl
    rewrite.many ltr "ap2" in "goal"
    rewrite ltr "IHx_0" in "goal"
    refl
  }

  "eigenvariables must return a proof's eigenvariables" in {

    eigenvariables( proof ) must beEqualTo( Set( hov"x:nat", hov"x_0:nat" ) )

  }
}
