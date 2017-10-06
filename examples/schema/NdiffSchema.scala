package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.PrimRecFun
import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._

object NdiffSchema extends TacticsProof {
  ctx += Context.InductiveType( "nat", hoc"0 : nat", hoc"s : nat>nat" )
  ctx += Context.Sort( "i" )
  ctx += hoc"f:i>nat"
  ctx += hoc"E: nat>nat>o"
  ctx += hoc"LE: i>i>o"
  ctx += hoc"LEQ: i>i>o"
  ctx += hoc"ADD: i>i>i"
  ctx += hoc"omega: nat>nat"
  ctx += hoc"phi: nat>nat>i>i>nat"
  ctx += hoc"chi: nat>nat>nat>i>nat"
  ctx += "nEqual" -> hos" E(f(B), f(A)), E(f(A), n),E(f(B), m) :-"
  ctx += PrimRecFun( hoc"DIFF:nat>i>o", "DIFF 0 x = (∃y (¬ (E (f x) (f y))))", "DIFF (s x) y = ( ∃z ( (¬ (E (f y) (f z))) ∧  (DIFF x z) ) )" )
  ctx += PrimRecFun( hoc"AP:nat>i>i", "AP 0 x = x", "AP (s x) y = (ADD y (AP x y))" )
  ctx += PrimRecFun(
    hoc"bloc:nat>nat>i>o",
    "bloc 0 x y = (∀z ( (LEQ (AP x y) z) ∧ (E (f z) x) ) )",
    "bloc (s x) y z = (∀w ( (LEQ (AP y z) w) ∧ (LE w (AP (s y) z)) ∧  (E (f w) y) ∧ (bloc x (s y) z) ))" )

  ctx += "SucNotEq" -> hcl"E(f(p),n),E(f(q),s(n)), E(f(p),f(q)) :- "
  ctx += "leq_refl" -> hos" :- LEQ(p,p)"
  ctx += "leq_g" -> hos"LEQ(AP(s(x),y),q):- LE(AP(x,y),q)"
  val esOmega = Sequent(
    Seq( hof"!x bloc(n,0,x)" ),
    Seq( hof"?p DIFF(n,p)" ) )
  ctx += Context.ProofNameDeclaration( le"omega n", esOmega )
  val eschi = Sequent(
    Seq( hof"bloc(n, m, a)" ),
    Seq( hof"∃x ∃y ( LEQ(AP(k,x), y) & E(f(y), k))" ) )
  ctx += Context.ProofNameDeclaration( le"chi n m k a", eschi )
  val esphi = Sequent(
    Seq( hof"E(f(B), n)", hof"bloc(n, m, K)" ),
    Seq( hof"DIFF(n, B)" ) )
  ctx += Context.ProofNameDeclaration( le"phi n m B K", esphi )
  val esOmegaSc = Sequent(
    Seq( "Ant_0" -> hof"!x bloc(s(n),0,x)" ),
    Seq( "Suc_0" -> hof"?p DIFF(s(n),p)" ) )
  val omegaSc = Lemma( esOmegaSc ) {
    cut( "cut", hof"?x ?y (LEQ(AP(s(n),x),y) &  E(f(y),s(n)))" )
    allL( "Ant_0", fov"K" )
    exR( "cut", fov"K" )
    ref( "chi" )
    exL( "cut", fov"A" )
    exL( "cut", fov"B" )
    andL( "cut" )
    allL( "Ant_0", fov"K" )
    exR( "Suc_0", fov"B" )
    ref( "phi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"omega (s n)", omegaSc )

  val esOmegaBc = Sequent(
    Seq( "Ant_0" -> hof"!x bloc(s(0),0,x)" ),
    Seq( "Suc_0" -> hof"?p DIFF(0,p)" ) )
  val omegaBc = Lemma( esOmegaBc ) {
    cut( "cut", hof"?x ?y (LEQ(AP(s(0),x),y) &  E(f(y),s(0)))" )
    allL( "Ant_0", fov"K" )
    ref( "chi" )
    exL( "cut", fov"K" )
    exL( "cut", fov"B" )
    allL( "Ant_0", fov"K" )
    exR( "Suc_0", fov"B" )
    andL( "cut" )
    unfold( "bloc" ) atMost 1 in "Ant_0_0"
    allL( "Ant_0_0", fov"B" )
    andL( "Ant_0_0_0" )
    andL( "Ant_0_0_0_0" )
    andL( "Ant_0_0_0_0_0" )
    ref( "phi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"omega 0", omegaBc )

  val esphiSc = Sequent(
    Seq( "Ant_0" -> hof"E(f(B), s(n))", "Ant_1" -> hof"bloc(s(n), m, K)" ),
    Seq( "Suc_0" -> hof"DIFF(s(n), B)" ) )
  val phiSc = Lemma( esphiSc ) {
    cut( "cut", hof"?x ?y (LEQ(AP(n,x),y) &  E(f(y),n))" )
    unfold( "bloc" ) atMost 1 in "Ant_1"
    allL( "Ant_1", le"t" )
    andL( "Ant_1_0" )
    andL( "Ant_1_0_0" )
    andL( "Ant_1_0_0_0" )
    ref( "chi" )
    unfold( "DIFF" ) atMost 1 in "Suc_0"
    unfold( "bloc" ) atMost 1 in "Ant_1"
    allL( "Ant_1", le"t" )
    andL( "Ant_1_0" )
    andL( "Ant_1_0_0" )
    andL( "Ant_1_0_0_0" )
    exL( "cut", fov"W" )
    exL( "cut", fov"A" )
    exR( "Suc_0", fov"A" )
    andR( "Suc_0_0" )
    andL( "cut" )
    negR( "Suc_0_0" )
    foTheory
    andL( "cut" )
    ref( "phi" )

  }
  ctx += Context.ProofDefinitionDeclaration( le"phi (s n) m B K", phiSc )

  val esphiBc = Sequent(
    Seq( "Ant_0" -> hof"E(f(B), s(0))", "Ant_1" -> hof"bloc(0, m, K)" ),
    Seq( "Suc_0" -> hof"DIFF(0, B)" ) )
  val phiBc = Lemma( esphiBc ) {
    unfold( "DIFF" ) atMost 1 in "Suc_0"
    unfold( "bloc" ) atMost 1 in "Ant_1"
    allL( "Ant_1", fov"A" )
    andL( "Ant_1_0" )
    exR( "Suc_0", fov"A" )
    negR( "Suc_0_0" )
    foTheory
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi 0 m B K", phiBc )

  val eschiSc = Sequent(
    Seq( "Ant_0" -> hof"bloc(s(n), m, K)" ),
    Seq( "Suc_0" -> hof"∃x ∃y ( LEQ(AP(k,x), y) & E(f(y), k))" ) )
  val chiSc = Lemma( eschiSc ) {
    unfold( "bloc" ) atMost 1 in "Ant_0"
    allL( "Ant_0", fov"B" )
    andL( "Ant_0_0" )
    andL( "Ant_0_0_0" )
    andL( "Ant_0_0_0_0" )
    ref( "chi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"chi (s n) m k K", chiSc )
  val eschiBc1 = Sequent(
    Seq( "Ant_0" -> hof"bloc(s(n), k, K)" ),
    Seq( "Suc_0" -> hof"∃x ∃y ( LEQ(AP(k,x), y) & E(f(y), k))" ) )
  val chiBc1 = Lemma( eschiBc1 ) {
    exR( "Suc_0", fov"K" )
    exR( "Suc_0_0", fov"B" )
    unfold( "bloc" ) atMost 1 in "Ant_0"
    allL( "Ant_0", fov"B" )
    andL( "Ant_0_0" )
    andL( "Ant_0_0_0" )
    andL( "Ant_0_0_0_0" )
    andR
    trivial
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"chi (s n) k k K", chiBc1 )
  val eschiBc2 = Sequent(
    Seq( "Ant_0" -> hof"bloc(0, k, K)" ),
    Seq( "Suc_0" -> hof"∃x ∃y ( LEQ(AP(k,x), y) & E(f(y), k))" ) )
  val chiBc2 = Lemma( eschiBc2 ) {

    exR( "Suc_0", fov"K" )
    exR( "Suc_0_0", fov"B" )
    unfold( "bloc" ) atMost 1 in "Ant_0"
    allL( "Ant_0", fov"B" )
    andL( "Ant_0_0" )
    andR
    trivial
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"chi 0 k k K", chiBc2 )
}

