package gapt.examples

import gapt.expr._
import gapt.proofs.Context._
import gapt.proofs.Context
import gapt.proofs.Sequent
import gapt.proofs.gaptic._

object GradedStrictMonotoneSchema extends TacticsProof {

  ctx += Context.InductiveType( "nat", hoc"0 : nat", hoc"s : nat>nat" )
  ctx += Context.Sort( "i" )
  ctx += hoc"f:i>nat"
  ctx += hoc"suc:i>i"
  ctx += hoc"z:i"
  ctx += hoc"E: nat>nat>o"
  ctx += hoc"LE: nat>nat>o"
  ctx += hoc"omega: nat>nat>nat"
  ctx += hoc"phi: nat>nat>nat"
  ctx += hoc"iLEQ:i>i>o"
  ctx += hoc"chi: nat>nat>i>nat"
  ctx += PrimRecFun( hoc"POR:nat>i>o", "POR 0 x = E 0 (f x) ", "POR (s y) x = (E (s y) (f x) ∨ POR y x)" )
  ctx += PrimRecFun( hoc"JumpSeq:nat>i>o", "JumpSeq 0 x = (E (f x), (f (suc x))) ", "JumpSeq (s y) x = ((E (f x) (f (suc x))) ∧ ∃p ((iLEQ (suc x) (suc p)) ∧ (JumpSeq y p) ))" )

  ctx += "LEDefinition" -> hos"POR(n,a) :- LE(f(a), s(n))"
  ctx += "LEDefinition2" -> hos"POR(n,suc(a)) :- LE(f(a), s(n))"
  ctx += "NumericTransitivity" -> hos"E(n,f(a)),E(n,f(suc(a))) :- E(f(a), f(suc(a)))"
  ctx += "minimalElement" -> hos"LE(f(z),0) :- "
  ctx += "reflexive" -> hos":- iLEQ(a,a)"
  ctx += "ordcon" -> hos"LE(f(a),s(n)) :- E(n,f(a)), LE(f(a),n)"
  ctx += "ordcon2" -> hos"LE(f(suc(a)),s(n)) :- E(n,f(suc(a))), LE(f(a),n)"

  val esOmega = Sequent(
    Seq( hof"!x POR(n,x)" ),
    Seq( hof"?x ( JumpSeq(k,x))" ) )
  ctx += Context.ProofNameDeclaration( le"omega n k", esOmega )
  val esPhi = Sequent(
    Seq( hof"?x ( E(n,f(x)) & E(n,f(suc(x)))) | !y (LE(f(y),n))" ),
    Seq( hof"?x (  JumpSeq(k,x) )" ) )
  ctx += Context.ProofNameDeclaration( le"phi n k", esPhi )
  val esChi = Sequent(
    Seq( hof"?x ( iLEQ(suc(a),suc(x)) & E(n,f(x)) & E(n,f(suc(x)))) | !y (iLEQ(suc(a),suc(y)) & LE(f(y),n))" ),
    Seq( hof"?x ( iLEQ(suc(a),suc(x)) & JumpSeq(k,x) )" ) )
  ctx += Context.ProofNameDeclaration( le"chi n k a", esChi )

  //The base case of  omega
  val esOmegaBc =
    Sequent(
      Seq( "Ant_0" -> hof"!x POR(0,x)" ),
      Seq( "Suc_0" -> hof"?x (JumpSeq(k,x))" ) )
  val omegaBc = Lemma( esOmegaBc ) {
    cut( "cut", hof"?x ( E(0,f(x)) & E(0,f(suc(x)))) | !y (LE(f(y),0))" )
    orR
    exR( "cut_0", hoc"z" )
    andR
    allL( "Ant_0", hoc"z" )
    unfold( "POR" ) atMost 1 in "Ant_0_0"
    trivial
    allL( "Ant_0", le"(suc z)" )
    unfold( "POR" ) atMost 1 in "Ant_0_0"
    trivial
    ref( "phi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"omega 0 k", omegaBc )

  val esOmegaSc =
    Sequent(
      Seq( "Ant_0" -> hof"!x POR(s(n),x)" ),
      Seq( "Suc_0" -> hof"?x ( JumpSeq(k,x))" ) )
  val omegaSc = Lemma( esOmegaSc ) {
    cut( "cut", hof"?x ( E(s(n),f(x)) & E(s(n),f(suc(x)))) | !y (LE(f(y),s(n)))" )
    orR
    allR( "cut_1", fov"a" )
    exR( "cut_0", fov"a" )
    andR
    allL( "Ant_0", fov"a" )
    unfold( "POR" ) atMost 1 in "Ant_0_0"
    orL
    trivial
    ref( "LEDefinition" )
    allL( "Ant_0", le"(suc a)" )
    unfold( "POR" ) atMost 1 in "Ant_0_0"
    orL
    trivial
    ref( "LEDefinition2" )
    ref( "phi" )

  }
  ctx += Context.ProofDefinitionDeclaration( le"omega (s n) k", omegaSc )
  val esPhiBc =
    Sequent(
      Seq( "Ant_0" -> hof"?x ( E(0,f(x)) & E(0,f(suc(x)))) | !y (LE(f(y),0))" ),
      Seq( "Suc_0" -> hof"?x (JumpSeq(0,x))" ) )
  val phiBc = Lemma( esPhiBc ) {
    orL
    exL( fov"a" )
    andL
    exR( fov"a" )
    unfold( "JumpSeq" ) atMost 1 in "Suc_0_0"
    ref( "NumericTransitivity" )
    allL( foc"z" )
    ref( "minimalElement" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi 0 0", phiBc )
  val esPhiBc1 =
    Sequent(
      Seq( "Ant_0" -> hof"?x ( E(0,f(x)) & E(0,f(suc(x)))) | !y (LE(f(y),0))" ),
      Seq( "Suc_0" -> hof"?x (JumpSeq(s(k),x))" ) )
  val phiBc1 = Lemma( esPhiBc1 ) {
    orL
    exL( fov"a" )
    andL
    unfold( "JumpSeq" ) atMost 1 in "Suc_0"
    exR( fov"a" )
    andR
    ref( "NumericTransitivity" )
    cut( "cut2", hof"?x (iLEQ(suc(a),suc(x)) & E(0,f(x)) & E(0,f(suc(x)))) | !y (iLEQ(suc(a),suc(y))  & LE(f(y),0))" )
    orR
    exR( "cut2_0", fov"a" )
    andR
    andR
    ref( "reflexive" )
    trivial
    trivial
    ref( "chi" )
    allL( foc"z" )
    ref( "minimalElement" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi 0 (s k)", phiBc1 )
  val esPhiSc =
    Sequent(
      Seq( "Ant_0" -> hof"?x ( E(s(n),f(x)) & E(s(n),f(suc(x)))) | !y (LE(f(y),s(n)))" ),
      Seq( "Suc_0" -> hof"?x ( JumpSeq(0,x))" ) )
  val phiSc = Lemma( esPhiSc ) {
    cut( "cut", hof"?x ( E(n,f(x)) & E(n,f(suc(x)))) | !y (LE(f(y),n))" )
    orR
    orL
    exL( fov"a" )
    andL
    exR( "Suc_0", fov"a" )
    unfold( "JumpSeq" ) atMost 1 in "Suc_0_0"
    ref( "NumericTransitivity" )
    allR( fov"b" )
    exR( "cut_0", fov"b" )
    allL( fov"b" )
    andR
    ref( "ordcon" )
    allL( le"(suc b)" )
    ref( "ordcon2" )
    ref( "phi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi (s n) 0 ", phiSc )
  val esPhiSc1 =
    Sequent(
      Seq( "Ant_0" -> hof"?x ( E(s(n),f(x)) & E(s(n),f(suc(x)))) | !y (LE(f(y),s(n)))" ),
      Seq( "Suc_0" -> hof"?x ( JumpSeq(s(k),x))" ) )
  val phiSc1 = Lemma( esPhiSc1 ) {
    cut( "cut", hof"?x ( E(n,f(x)) & E(n,f(suc(x)))) | !y (LE(f(y),n))" )
    orR
    orL
    exL( fov"a" )
    andL
    unfold( "JumpSeq" ) atMost 1 in "Suc_0"
    exR( "Suc_0", fov"a" )
    andR
    ref( "NumericTransitivity" )
    cut( "cut2", hof"?x (iLEQ(suc(a),suc(x)) & E(s(n),f(x)) & E(s(n),f(suc(x)))) | !y (iLEQ(suc(a),suc(y)) & LE(f(y),s(n)))" )
    orR
    exR( "cut2_0", fov"a" )
    andR
    andR
    ref( "reflexive" )
    trivial
    trivial
    ref( "chi" )
    allR( fov"b" )
    exR( "cut_0", fov"b" )
    allL( fov"b" )
    andR
    ref( "ordcon" )
    allL( le"(suc b)" )
    ref( "ordcon2" )
    ref( "phi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi (s n) (s k)", phiSc1 )

  val esChiBc =
    Sequent(
      Seq( "Ant_0" -> hof"?x (iLEQ(suc(a),suc(x)) & E(0,f(x)) & E(0,f(suc(x)))) | !y (iLEQ(suc(a),suc(y)) & LE(f(y),0))" ),
      Seq( "Suc_0" -> hof"?x ( iLEQ(suc(a),suc(x)) & JumpSeq(0,x))" ) )
  val chiBc = Lemma( esChiBc ) {
    orL
    exL( fov"b" )
    andL
    andL
    exR( fov"b" )
    andR
    trivial
    unfold( "JumpSeq" ) in "Suc_0_0"
    ref( "NumericTransitivity" )
    allL( foc"z" )
    andL
    ref( "minimalElement" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"chi 0 0 a", chiBc )
  val esChi1Bc =
    Sequent(
      Seq( "Ant_0" -> hof"?x (iLEQ(suc(a),suc(x)) & E(0,f(x)) & E(0,f(suc(x)))) | !y (iLEQ(suc(a),suc(y)) & LE(f(y),0))" ),
      Seq( "Suc_0" -> hof"?x ( iLEQ(suc(a),suc(x)) & JumpSeq(s(k),x))" ) )
  val chi1Bc = Lemma( esChi1Bc ) {
    orL
    exL( fov"b" )
    andL
    andL
    exR( fov"b" )
    andR
    trivial
    unfold( "JumpSeq" ) atMost 1 in "Suc_0_0"
    andR
    ref( "NumericTransitivity" )
    cut( "cut2", hof"?x (iLEQ(suc(b),suc(x)) & E(0,f(x)) & E(0,f(suc(x)))) | !y (iLEQ(suc(b),suc(y))  & LE(f(y),0))" )
    orR
    exR( "cut2_0", fov"b" )
    andR
    andR
    ref( "reflexive" )
    trivial
    trivial
    ref( "chi" )
    allL( foc"z" )
    andL
    ref( "minimalElement" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"chi 0 (s k) a", chi1Bc )

  val esChiSc =
    Sequent(
      Seq( "Ant_0" -> hof"?x (  iLEQ(suc(a),suc(x)) & E(s(n),f(x)) & E(s(n),f(suc(x)))) | !y (iLEQ(suc(a),suc(y)) & LE(f(y),s(n)))" ),
      Seq( "Suc_0" -> hof"?x (  iLEQ(suc(a),suc(x)) & JumpSeq(0,x) )" ) )
  val ChiSc = Lemma( esChiSc ) {
    cut( "cut", hof"?x ( iLEQ(suc(a),suc(x)) & E(n,f(x)) & E(n,f(suc(x)))) | !y (iLEQ(suc(a),suc(y)) & LE(f(y),n))" )
    orR
    orL
    exL( fov"b" )
    andL
    andL
    exR( "Suc_0", fov"b" )
    andR
    trivial
    unfold( "JumpSeq" ) in "Suc_0_0"
    ref( "NumericTransitivity" )
    allR( fov"c" )
    exR( "cut_0", fov"c" )
    allL( fov"c" )
    andL
    andR( "cut_1" )
    trivial
    andR( "cut_0_0" )
    andR( "cut_0_0" )
    trivial
    ref( "ordcon" )
    allL( le"(suc c)" )
    andL( "Ant_0_1" )
    ref( "ordcon2" )
    forget( "Ant_0" )
    ref( "chi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"chi (s n) 0 a", ChiSc )

  val esChi1Sc =
    Sequent(
      Seq( "Ant_0" -> hof"?x (  iLEQ(suc(a),suc(x)) & E(s(n),f(x)) & E(s(n),f(suc(x)))) | !y (iLEQ(suc(a),suc(y)) & LE(f(y),s(n)))" ),
      Seq( "Suc_0" -> hof"?x ( iLEQ(suc(a),suc(x)) & JumpSeq(s(k),x))" ) )
  val chi1Sc = Lemma( esChi1Sc ) {
    cut( "cut", hof"?x ( iLEQ(suc(a),suc(x)) & E(n,f(x)) & E(n,f(suc(x)))) | !y (iLEQ(suc(a),suc(y))& LE(f(y),n))" )
    orR
    orL
    exL( fov"b" )
    andL
    andL
    exR( "Suc_0", fov"b" )
    andR
    trivial
    unfold( "JumpSeq" ) atMost 1 in "Suc_0_0"
    andR
    ref( "NumericTransitivity" )
    cut( "cut2", hof"?x (iLEQ(suc(b),suc(x)) & E(s(n),f(x)) & E(s(n),f(suc(x)))) | !y (iLEQ(suc(b),suc(y)) & LE(f(y),s(n)))" )
    orR
    exR( "cut2_0", fov"b" )
    andR
    andR
    ref( "reflexive" )
    trivial
    trivial
    ref( "chi" )
    allR( fov"b" )
    exR( "cut_0", fov"b" )
    allL( fov"b" )
    andL
    andR( "cut_1" )
    trivial
    andR
    andR
    trivial
    ref( "ordcon" )
    allL( le"(suc b)" )
    andL( "Ant_0_1" )
    ref( "ordcon2" )
    ref( "chi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"chi (s n) (s k) a", chi1Sc )

}

