package at.logic.gapt.examples
import at.logic.gapt.expr._
import at.logic.gapt.proofs.lk.TheoryAxiom
import at.logic.gapt.proofs.{ Context, FiniteContext, Sequent }
import at.logic.gapt.proofs.gaptic._

object primediv extends TacticsProof {

  implicit var ctx = FiniteContext()
  ctx += Context.Sort( "nat" )
  ctx += hoc"'*': nat>nat>nat"
  ctx += hoc"1: nat"
  ctx += hoc"'<': nat>nat>o"

  val theory =
    ( "assoc" -> hof"∀x∀y∀z x*(y*z) = (x*y)*z" ) +:
      ( "neutral" -> hof"∀x x*1 = x" ) +:
      ( "mulleq" -> hof"∀x∀y∀z (x*y=z ∧ x!=1 ⊃ x<z)" ) +:
      ( "oneleqeq" -> hof"∀x (x!=1 ⊃ 1<x)" ) +:
      Sequent()

  ctx += hof"LNP = (∀X (∃y X y ⊃ ∃y (X y ∧ ∀z (z < y ⊃ ¬X z))))"
  ctx += hof"IND = (∀X ((∀y (∀z (z < y ⊃ X z) ⊃ X y)) ⊃ ∀y X y))"
  ctx += hof"D w y = (∃z w*z = y)"
  ctx += hof"(x > y) = (y < x)"
  ctx += hof"PRIME w = (w > 1 ∧ ∀z (D z w ⊃ z=1 ∨ z=w))"
  ctx += hof"PD w y = (PRIME w ∧ D w y)"

  // TODO: expose current BabelSignature inside Lemma, then we can drop the (x:nat) annotation
  // TODO: weak quantifier tactics should provide a mode to forget the old formula immediately, and NOT change the label

  val lnpind = Lemma( ( "lnp" -> hof"LNP" ) +: Sequent() :+ ( "ind" -> hof"IND" ) ) {
    unfold( "lnp", "LNP" )
    unfold( "ind", "IND" )
    decompose
    allL( "lnp", le"λ(x:nat) ¬X x" ); forget( "lnp" )
    destruct( "lnp_0" )
    exR( "lnp_0", le"y:nat" ); prop
    decompose
    chain( "ind_0" ).at( "lnp_0_0" )
    decompose
    allL( "lnp_0_1", le"z:nat" )
    prop
  }

  val proof = Lemma( ( "lnp" -> hof"LNP" ) +: theory :+ ( "goal" -> hof"∀y (y > 1 ⊃ ∃w PD w y)" ) ) {
    include( "ind", lnpind ); unfold( "ind", "IND" )
    allL( "ind", le"λu (u > 1 ⊃ ∃w PD w u)" )
    chain( "ind_0" ); decompose

    cut( "yprime", hof"PRIME y" )

    // case b
    unfold( "yprime", "PRIME", "D" )
    destruct( "yprime" ); prop; decompose
    allL( "goal_0", le"z:nat" )
    destruct( "goal_0_0" ); chain( "mulleq" ).at( "goal_0_0" ).subst( hov"y:nat" -> le"z_0:nat" ); prop; prop
    destruct( "goal_0_0" ); unfold( "goal_0_0", ">" ); chain( "oneleqeq" ).at( "goal_0_0" ); prop
    decompose; exR( le"w:nat" ); forget( "goal_1_1" )
    unfold( "goal_0_0", "PD", "D" ); unfold( "goal_1_1_0", "PD", "D" )
    destruct( "goal_1_1_0" ); prop; decompose
    exR( le"z_1*z_0" )
    rewrite.many ltr ( "assoc", "goal_0_0_1" ) in "goal_1_1_0_0"; trivial

    // case a
    unfold( "goal_1_1", "PD" )
    exR( le"y: nat" ); destruct( "goal_1_1_0" ); prop
    unfold( "goal_1_1_0", "D" )
    exR( "goal_1_1_0", le"1" )
    rewrite ltr "neutral" in "goal_1_1_0_0"
    refl
  }

  val defs = ctx.definitions
}
