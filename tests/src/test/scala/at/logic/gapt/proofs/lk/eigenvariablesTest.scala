package at.logic.gapt.proofs.lk

import gapt.expr._
import gapt.formats.babel.Notation
import gapt.formats.babel.Precedence
import gapt.proofs.context.MutableContext
import gapt.proofs.gaptic._
import gapt.proofs.lk.EigenVariablesLK
import gapt.proofs.Sequent
import gapt.proofs.context.Context
import gapt.proofs.context.update.InductiveType
import org.specs2.mutable._

class eigenvariablesTest extends Specification {

  implicit var ctx: MutableContext = Context().newMutable
  ctx += InductiveType( "nat", hoc"0: nat", hoc"s:nat>nat" )
  ctx += Notation.Infix( "+", Precedence.plusMinus )
  ctx += hoc"'+': nat>nat>nat"

  val plus_axioms = Seq(
    "ap1" -> hof"∀y 0+y = y",
    "ap2" -> hof"∀x∀y s(x)+y = s(x+y)" )

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

    EigenVariablesLK( proof ) must beEqualTo( Set( hov"x:nat", hov"x_0:nat" ) )

  }
}
