package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.PrimRecFun
import at.logic.gapt.proofs.{ Context, Sequent }
import at.logic.gapt.proofs.gaptic.TacticsProof
import at.logic.gapt.proofs.gaptic._

object StrongStrictMonotoneSchema extends TacticsProof {
  ctx += Context.InductiveType( "nat", hoc"0 : nat", hoc"s : nat>nat" )
  ctx += Context.Sort( "i" )
  ctx += hoc"f:i>nat"
  ctx += hoc"suc:i>i"
  ctx += hoc"z:i"
  ctx += hoc"E: nat>nat>o"
  ctx += hoc"Eq: i>i>o"
  ctx += hoc"LE: nat>nat>o"
  ctx += hoc"LEQ: nat>nat>o"
  ctx += hoc"iLEQ: i>i>o"

  ctx += hoc"omega: nat>nat"
  ctx += hoc"phi: nat>nat"
  ctx += PrimRecFun( hoc"POR:nat>i>o", "POR 0 x = E 0 (f x) ", "POR (s y) x = (E (s y) (f x) ∨ POR y x)" )
  ctx += "LEDefinition" -> hos"POR(n,a) :- LE(f(a), s(n))"
  ctx += "monotonicity" -> hos"POR(n,a) :- LE(f(suc(a)), s(n))"
  ctx += "NumericTransitivity" -> hos"E(n,f(a)),E(n,f(suc(a))) :- E(f(a), f(suc(a)))"
  ctx += "minimalElement" -> hos"LE(n,0) :- "
  ctx += "reflexivity" -> hos" :- iLEQ(a,a)"
  ctx += "OrderPrinciple" -> hos"LE(f(suc(a)),s(n)) :- E(f(a),f(suc(a))), LE(f(suc(a)),n)"

  val esOmega = Sequent(
    Seq( hof"!x POR(n,x)" ),
    Seq( hof"?x ( E(f(x), f(suc(x))) )" ) )
  ctx += Context.ProofNameDeclaration( le"omega n", esOmega )
  val esPhi = Sequent(
    Seq( hof"?x ( E(f(x), f(suc(x))) | LE(f(suc(x)),n))" ),
    Seq( hof"?x ( E(f(x), f(suc(x))) )" ) )
  ctx += Context.ProofNameDeclaration( le"phi n", esPhi )

  //The base case of  omega
  val esOmegaBc =
    Sequent(
      Seq( "Ant_0" -> hof"!x POR(0,x)" ),
      Seq( "Suc_0" -> hof"?x (E(f(x), f(suc(x))))" ) )
  val omegaBc = Lemma( esOmegaBc ) {
    cut( "cut", hof"?x ( E(f(x), f(suc(x))) | LE(f(suc(x)),0))" )
    exR( "cut", hoc"z" )
    allL( hoc"z" )
    allL( le"(suc z)" )
    unfold( "POR" ) atMost 1 in "Ant_0_0"
    unfold( "POR" ) atMost 1 in "Ant_0_1"
    orR
    ref( "NumericTransitivity" )
    ref( "phi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"omega 0", omegaBc )
  val esOmegaSc =
    Sequent(
      Seq( "Ant_0" -> hof"!x POR(s(n),x)" ),
      Seq( "Suc_0" -> hof"?x (E(f(x), f(suc(x))))" ) )
  val omegaSc = Lemma( esOmegaSc ) {
    cut( "cut", hof"?x ( E(f(x), f(suc(x))) | LE(f(suc(x)),s(n)))" )
    exR( "cut", hoc"z" )
    allL( hoc"z" )
    allL( le"(suc z)" )
    unfold( "POR" ) atMost 1 in "Ant_0_0"
    unfold( "POR" ) atMost 1 in "Ant_0_1"
    orR
    orL( "Ant_0_1" )
    exR( "cut", hoc"z" )
    orR
    orL
    ref( "NumericTransitivity" )
    ref( "monotonicity" )
    ref( "LEDefinition" )
    ref( "phi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"omega (s n)", omegaSc )

  val esPhiBc =
    Sequent(
      Seq( "Ant_0" -> hof"?x ( E(f(x), f(suc(x))) | LE(f(suc(x)),0))" ),
      Seq( "Suc_0" -> hof"?x (E(f(x), f(suc(x))) )" ) )
  val phiBc = Lemma( esPhiBc ) {
    exL( fov"a" )
    exR( fov"a" )
    orL( "Ant_0" )
    trivial
    ref( "minimalElement" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi 0", phiBc )

  val esPhiSc =
    Sequent(
      Seq( "Ant_0" -> hof"?x ( E(f(x), f(suc(x))) | LE(f(suc(x)),s(n)))" ),
      Seq( "Suc_0" -> hof"?x (E(f(x), f(suc(x))) )" ) )
  val phiSc = Lemma( esPhiSc ) {
    cut( "cut", hof"?x ( E(f(x), f(suc(x))) | LE(f(suc(x)), n) )" )
    exL( fov"a" )
    exR( "cut", fov"a" )
    orR
    orL
    exR( "cut", fov"a" )
    orR
    trivial
    ref( "OrderPrinciple" )
    ref( "phi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi (s n)", phiSc )

}

