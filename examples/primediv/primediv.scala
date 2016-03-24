package at.logic.gapt.examples
import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Context, FiniteContext, Sequent }
import at.logic.gapt.proofs.gaptic._

object primediv extends TacticsProof {
  ctx += Context.Sort( "nat" )
  ctx += hoc"'*': nat>nat>nat"
  ctx += hoc"1: nat"
  ctx += hoc"'<': nat>nat>o"

  val theory =
    ( "assoc" -> hof"∀x∀y∀z x*(y*z) = (x*y)*z" ) +:
      ( "neutral" -> hof"∀x x*1 = x" ) +:
      ( "mulleq" -> hof"∀x∀y∀z (x*y=z ∧ x!=z ⊃ x<z)" ) +:
      ( "oneleqeq" -> hof"∀x (x!=1 ⊃ 1<x)" ) +:
      Sequent()

  ctx += hof"LNP = (∀X (∃y X y ⊃ ∃y (X y ∧ ∀z (z < y ⊃ ¬X z))))"
  ctx += hof"IND = (∀X ((∀y (∀z (z < y ⊃ X z) ⊃ X y)) ⊃ ∀y X y))"
  ctx += hof"D w y = (∃z w*z = y)"
  ctx += hof"(x > y) = (y < x)"
  ctx += hof"PRIME w = (w > 1 ∧ ∀z (D z w ⊃ z=1 ∨ z=w))"
  ctx += hof"PD w y = (PRIME w ∧ D w y)"

  // TODO: expose current BabelSignature inside Lemma, then we can drop the (x:nat) annotation

  val lnpind = Lemma( ( "lnp" -> hof"LNP" ) +: Sequent() :+ ( "ind" -> hof"IND" ) ) {
    unfold( "LNP" ) in "lnp"; unfold( "IND" ) in "ind"; decompose
    allL( "lnp", le"λ(x:nat) ¬X x" ).forget; destruct( "lnp" )
    exR( "lnp", le"y:nat" ); prop
    decompose; chain( "ind_0" ).at( "lnp_0" )
    decompose; allL( "lnp_1", le"z:nat" ); prop
  }

  val proof = Lemma( ( "lnp" -> hof"LNP" ) +: theory :+ ( "goal" -> hof"∀y (y > 1 ⊃ ∃w PD w y)" ) ) {
    include( "ind", lnpind ); unfold( "IND" ) in "ind"
    allL( "ind", le"λu (u > 1 ⊃ ∃w PD w u)" )
    chain( "ind_0" ); decompose

    cut( "yprime", hof"PRIME y" )

    // case b
    repeat( unfold( "PRIME", "D" ) in "yprime" )
    destruct( "yprime" ); prop; decompose
    allL( "goal_0", le"z:nat" ).forget
    destruct( "goal_0" ); chain( "mulleq" ).at( "goal_0" ).subst( hov"y:nat" -> le"z_0:nat" ); prop; prop
    destruct( "goal_0" ); unfold( ">" ) in "goal_0"; chain( "oneleqeq" ).at( "goal_0" ); prop
    decompose; exR( le"w:nat" ).forget
    repeat( unfold( "PD", "D" ) in ( "goal_0", "goal_1_1" ) )
    destruct( "goal_1_1" ); prop; decompose
    exR( le"z_1*z_0" ).forget
    rewrite.many ltr ( "assoc", "goal_0_1" ) in "goal_1_1"; trivial

    // case a
    unfold( "PD" ) in "goal_1_1"
    exR( le"y: nat" ).forget; destruct( "goal_1_1" ); prop
    unfold( "D" ) in "goal_1_1"
    exR( "goal_1_1", le"1" ).forget
    rewrite ltr "neutral" in "goal_1_1"
    refl
  }

  val defs = ctx.definitions
}
