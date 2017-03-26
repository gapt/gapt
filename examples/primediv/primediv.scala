package at.logic.gapt.examples
import at.logic.gapt.expr._
import at.logic.gapt.proofs.{ Context, Sequent }
import at.logic.gapt.proofs.gaptic._

object primediv extends TacticsProof {
  ctx += Context.Sort( "nat" )
  ctx += hoc"'*': nat>nat>nat"
  ctx += hoc"1: nat"
  ctx += hoc"'<': nat>nat>o"

  val theory = hols"""
      assoc: ∀x∀y∀z x*(y*z) = (x*y)*z,
      neutral: ∀x x*1 = x,
      mulleq: ∀x∀y∀z (x*y=z ∧ x!=z ⊃ x<z),
      oneleqeq: ∀x (x!=1 ⊃ 1<x) :-
    """

  ctx += hof"LNP = (∀X (∃y X y ⊃ ∃y (X y ∧ ∀z (z < y ⊃ ¬X z))))"
  ctx += hof"IND = (∀X ((∀y (∀z (z < y ⊃ X z) ⊃ X y)) ⊃ ∀y X y))"
  ctx += hof"D w y = (∃z w*z = y)"
  ctx += hof"(x > y) = (y < x)"
  ctx += hof"PRIME w = (w > 1 ∧ ∀z (D z w ⊃ z=1 ∨ z=w))"
  ctx += hof"PD w y = (PRIME w ∧ D w y)"

  // TODO: expose current BabelSignature inside Lemma, then we can drop the (x:nat) annotation

  val lnpind = Lemma( hols"LNP :- IND" ) {
    unfold( "LNP" ) in "LNP"; unfold( "IND" ) in "IND"; decompose
    allL( "LNP", le"λ(x:nat) ¬X x" ).forget; destruct( "LNP" )
    exR( "LNP", le"y:nat" ); prop
    decompose; chain( "IND_0" ).at( "LNP_0" )
    decompose; allL( "LNP_1", le"z:nat" ); prop
  }

  val proof = Lemma( theory ++ hols"LNP :- ∀y (y > 1 ⊃ ∃w PD w y)" ) {
    include( "ind", lnpind ); unfold( "IND" ) in "ind"
    allL( "ind", le"λu (u > 1 ⊃ ∃w PD w u)" )
    chain( "ind_0" ); decompose

    cut( "yprime", hof"PRIME y" )

    // case b
    unfold( "PRIME", "D" ) in "yprime"
    destruct( "yprime" ); prop; decompose
    allL( "g_0", le"z:nat" ).forget
    destruct( "g_0" ); chain( "mulleq" ).at( "g_0" ).subst( hov"y:nat" -> le"z_0:nat" ); prop; prop
    destruct( "g_0" ); unfold( ">" ) in "g_0"; chain( "oneleqeq" ).at( "g_0" ); prop
    decompose; exR( le"w:nat" ).forget
    unfold( "PD", "D" ) in ( "g_0", "g_1_1" )
    destruct( "g_1_1" ); prop; decompose
    exR( le"z_1*z_0" ).forget
    rewrite.many ltr ( "assoc", "g_0_1" ) in "g_1_1"; trivial

    // case a
    unfold( "PD" ) in "g_1_1"
    exR( le"y: nat" ).forget; destruct( "g_1_1" ); prop
    unfold( "D" ) in "g_1_1"
    exR( "g_1_1", le"1" ).forget
    rewrite ltr "neutral" in "g_1_1"
    refl
  }
}
