package at.logic.gapt.proofs.lk

import at.logic.gapt.expr._
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.{ Context, Sequent }
import org.specs2.mutable.Specification

class extractInductionAxiomsTest extends Specification {

  implicit var ctx = Context()
  ctx += Context.InductiveType( "nat", hoc"0: nat", hoc"s:nat>nat" )
  ctx += hoc"'+': nat>nat>nat"

  val plus_axioms = Seq(
    ( "ap1" -> hof"∀y 0+y = y" ),
    ( "ap2" -> hof"∀x∀y s(x)+y = s(x+y)" )
  )

  val plusCommutativityProof = Lemma( plus_axioms ++: Sequent() :+
    ( "goal" -> hof"∀x∀y x + y = y + x" ) ) {
    allR
    induction( hov"x:nat" )
    allR
    rewrite ltr "ap1" in "goal"
    induction( hov"y:nat" )
    rewrite ltr "ap1" in "goal"
    refl
    rewrite ltr "ap2" in "goal"
    quasiprop
    allR
    induction( hov"y:nat" )
    rewrite ltr "ap2" in "goal"
    rewrite ltr "IHx_0" in "goal"
    rewrite.many ltr "ap1" in "goal"
    refl
    rewrite.many ltr "ap2" in "goal"
    rewrite ltr "IHx_0" in "goal"
    rewrite rtl "IHy_0" in "goal"
    rewrite.many ltr "ap2" in "goal"
    rewrite ltr "IHx_0" in "goal"
    refl
  }

  "free non-eigenvariable variables should not be bound" in {
    val proof = Lemma( plus_axioms ++: Sequent() :+
      ( "goal" -> hof"x + (y + z) = (x + y) + z" ) ) {
      induction( hov"x:nat" )
      rewrite.many ltr "ap1" in "goal"
      refl
      rewrite.many ltr "ap2" in "goal"
      rewrite ltr "IHx_0" in "goal"
      refl
    }
    freeVariables( extractInductionAxioms( proof )( ctx )( 0 ) ) must beEqualTo(
      Set( hov"y:nat", hov"z:nat" )
    )
  }

  "eigenvariables should be bound" in {
    val eigenVars = eigenvariables( plusCommutativityProof )
    val freeVars = extractInductionAxioms( plusCommutativityProof ).map( freeVariables( _ ) ).toSet.flatten
    eigenVars.foreach { ev =>
      if ( freeVars.contains( ev ) ) {
        failure( s"$ev occurs freely in extracted induction axiom" )
      }
    }
    success
  }

  "all induction axioms should be extracted" in {
    val expectedAxioms = Seq(
      hof"(⊤ ⊃ !y 0 + y = y + 0) ∧ !x (!y x + y = y + x ⊃ !y s(x) + y = y + s(x)) ⊃ !x !y x + y = y + x",
      hof"(⊤ ⊃ 0 = 0 + 0) ∧ !y (y = y + 0 ⊃ s(y) = s(y) + 0) ⊃ !y y = y + 0",
      hof"!x ((⊤ ⊃ s(x) + 0 = 0 + s(x)) ∧ !y (s(x) + y = y + s(x) ⊃ s(x) + s(y) = s(y) + s(x)) ⊃ !y s(x) + y = y + s(x))"
    )
    val axioms = extractInductionAxioms( plusCommutativityProof )
    if ( expectedAxioms.size != axioms.size ) {
      failure( "too many or too few axioms were extracted" )
    }
    axioms foreach { axiom =>
      if ( expectedAxioms.filter( _.alphaEquals( axiom ) ).isEmpty ) {
        failure( s"$axiom does not correspond to any expected axiom" )
      }
    }
    success
  }
}
