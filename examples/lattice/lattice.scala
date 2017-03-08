package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.expr.hol.CNFp
import at.logic.gapt.proofs.{ Context, Sequent }
import at.logic.gapt.proofs.gaptic._

object lattice extends TacticsProof {
  ctx += Context.Sort( "i" )
  ctx += hoc"cap: i>i>i"
  ctx += hoc"cup: i>i>i"

  Seq(
    hof"∀x∀y cap x y = cap y x",
    hof"∀x∀y∀z cap (cap x y) z = cap x (cap y z)",
    hof"∀x cap x x = x",
    hof"∀x∀y cup x y = cup y x",
    hof"∀x∀y∀z cup (cup x y) z = cup x (cup y z)",
    hof"∀x cup x x = x"
  ).flatMap( CNFp( _ ) ).foreach( ctx += _ )

  ctx += hof"(x <= y) = (cap x y = x)"
  ctx += hof"L1 = (∀x∀y (cap x y = x <-> cup x y = y))"
  ctx += hof"L2 = (∀x∀y cup (cap x y) x = x ∧ ∀x∀y cap (cup x y) x = x)"
  ctx += hof"R = (∀x x<=x)"
  ctx += hof"AS = (∀x∀y (x<=y ∧ y<=x ⊃ x=y))"
  ctx += hof"T = (∀x∀y∀z (x<=y ∧ y<=z ⊃ x<=z))"
  ctx += hof"POSET = (R & (AS & T))"
  ctx += hof"GLB = (∀x∀y (cap x y <= x ∧ cap x y <= y ∧ ∀z (z<=x ∧ z<=y ⊃ z <= cap x y)))"
  ctx += hof"LUB = (∀x∀y (x <= cup x y ∧ y <= cup x y ∧ ∀z (x<=z ∧ y<=z ⊃ cup x y <= z)))"
  ctx += hof"L3 = (POSET ∧ (GLB ∧ LUB))"

  val defs = ctx.definitions.toMap

  //
  // Left sub proof
  //

  // show that join is _least_ upper bound for \leq
  val p_6 = Lemma( hols"L1 :- ∀z (x_0 <= z ∧ y_0 <= z ⊃ cup x_0 y_0 <= z)" ) {
    unfold( "<=" ) in "g"
    allR( hov"z_0" )
    impR
    andL
    unfold( "L1" ) in "L1"
    allL( "L1", le"x_0", le"z_0" )
    andL( "L1_0" )
    impL( "L1_0_0" )
    prop
    allL( "L1", le"y_0", le"z_0" )
    andL( "L1_1" )
    impL( "L1_1_0" )
    prop
    allL( "L1", le"cup x_0 y_0", le"z_0" )
    andL( "L1_2" )
    impL( "L1_2_1" )
    foTheory
    prop
  }

  // continues showing that join is upper bound for \leq
  val p_5_1 = Lemma( hols"L1 :- x <= cup x y" ) {
    unfold( "<=" ) in "g"
    unfold( "L1" ) in "L1"
    allL( "L1", le"x", le"cup x y" )
    andL
    impL( "L1_0_1" )
    foTheory
    prop
  }

  // show that join is upper bound for \leq
  val p_5 = Lemma( hols"L1 :- LUB" ) {
    unfold( "LUB" ) in "LUB"
    allR( "LUB", hov"x_0" )
    allR( "LUB", hov"y_0" )
    andR
    andR
    insert( p_5_1 )
    cut( "cupcomm", hof"cup x_0 y_0 = cup y_0 x_0" ); foTheory
    rewrite ltr "cupcomm" in "LUB"
    insert( p_5_1 )
    insert( p_6 )
  }

  //show that meet is _greatest_ lower bound for \leq
  val p_4 = Lemma( hols":- ∀z (z <= x_0 ∧ z <= y_0 ⊃ z <= cap x_0 y_0)" ) {
    unfold( "<=" ) in "g"
    decompose
    foTheory
  }

  // finishes showing that meet is lower bound for \leq
  val p_3_1 = Lemma( hols":- cap x_0 y_0 <= y_0" ) {
    unfold( "<=" ) in "g"
    foTheory
  }

  // show that meet is lower bound for \leq
  val p_3 = Lemma( hols"L1 :- GLB & LUB" ) {
    andR
    unfold( "GLB" ) in "g"
    decompose
    andR
    andR
    unfold( "<=" ) in "g"; foTheory
    insert( p_3_1 )
    insert( p_4 )
    insert( p_5 )
  }

  // show transitivity
  val p_2 = Lemma( hols":- T" ) {
    unfold( "T" ) in "T"
    decompose
    unfold( "<=" ) in ( "T_0_0", "T_0_1", "T_1" )
    foTheory
  }

  // show anti-symmetry
  val p_1 = Lemma( hols":- AS & T" ) {
    andR
    unfold( "AS" ) in "g"
    decompose
    unfold( "<=" ) in ( "g_0_0", "g_0_1" ); foTheory
    insert( p_2 )
  }

  // split up POSET, show reflexivity
  val p1_3 = Lemma( hols"L1 :- L3" ) {
    unfold( "L3" ) in "L3"
    andR
    unfold( "POSET" ) in "L3"
    andR
    unfold( "R", "<=" ) in "L3"
    decompose
    foTheory
    insert( p_1 )
    insert( p_3 )
  }

  //
  // Right sub proof
  //

  // finishes r_2
  val r_2_1 = Lemma( hols"LUB :- x_0 <= cup x_0 y_0" ) {
    unfold( "LUB" ) in "LUB"
    allL( "LUB", hov"x_0", hov"y_0" )
    andL
    andL
    axiomLog
  }

  // absorption law 2 - difficult direction
  val r_2 = Lemma(
    hols"""LUB, R, ∀z (z <= cup x_0 y_0 ∧ z <= x_0 ⊃ z <= cap (cup x_0 y_0) x_0) :-
      x_0 <= cap (cup x_0 y_0) x_0"""
  ) {
      allL( "h_0", le"x_0" )
      impL
      andR
      insert( r_2_1 )
      unfold( "R" ) in "R"
      allL( "R", le"x_0" )
      axiomLog
      prop
    }

  // apply anti-symmetry to show absorption law 2 (+ easy direction)
  val q_2 = Lemma( hols"GLB, LUB, R, AS :- ∀x∀y cap (cup x y) x = x" ) {
    decompose
    unfold( "GLB" ) in "GLB"; allL( "GLB", le"cup x y", le"x" ); decompose
    unfold( "AS" ) in "AS"; chain( "AS" )
    trivial
    insert( r_2 )
  }

  // finishes r_1
  val r_1_1 = Lemma( hols"GLB :- cap x_0 y_0 <= x_0" ) {
    unfold( "GLB" ) in "GLB"
    allL( "GLB", le"x_0", le"y_0" )
    forget( "GLB" )
    andL( "GLB_0" )
    andL( "GLB_0_0" )
    axiomLog
  }

  // absorption law 1 - difficult direction
  val r_1 = Lemma( hols"""
    GLB, R, ∀z (cap x_0 y_0 <= z ∧ x_0 <= z ⊃ cup (cap x_0 y_0) x_0 <= z) :-
    cup (cap x_0 y_0) x_0 <= x_0
    """ ) {
    chain( "h_0" )
    insert( r_1_1 )
    unfold( "R" ) in "R"
    chain( "R" )
  }

  // apply anti-symmetry to show absorption law 1 (+ easy direction)
  val q_1 = Lemma( hols"GLB, LUB, R, AS :- ∀x∀y (cup (cap x y) x = x)" ) {
    decompose
    unfold( "AS" ) in "AS"
    allL( "AS", le"cup (cap x y) x", le"x" )
    forget( "AS" )
    impL( "AS_0" )
    unfold( "LUB" ) in "LUB"
    allL( "LUB", le"cap x y", le"x" )
    forget( "LUB" )
    andL( "LUB_0" )
    andL( "LUB_0_0" )
    andR
    insert( r_1 )
    axiomLog
    axiomLog
  }

  val p3_2 = Lemma( hols"L3 :- L2" ) {
    unfold( "L3" ) in "L3"
    decompose
    unfold( "POSET" ) in "L3_0"
    decompose
    unfold( "L2" ) in "L2"
    andR
    insert( q_1 )
    insert( q_2 )
  }

  // Main proof
  val p = Lemma( hols"L1 :- L2" ) {
    cut( "L3", hof"L3" )
    insert( p1_3 )
    insert( p3_2 )
  }
}
