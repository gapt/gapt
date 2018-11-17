package gapt.examples

import gapt.expr._
import gapt.proofs.Sequent
import gapt.proofs.context.update.InductiveType
import gapt.proofs.context.update.{ PrimitiveRecursiveFunction => PrimRecFun }
import gapt.proofs.context.update.ProofDefinitionDeclaration
import gapt.proofs.context.update.ProofNameDeclaration
import gapt.proofs.context.update.Sort
import gapt.proofs.gaptic._

object ThreeStrictMonotoneSchema extends TacticsProof {

  ctx += InductiveType( "nat", hoc"0 : nat", hoc"s : nat>nat" )
  ctx += Sort( "i" )
  ctx += hoc"f:i>nat"
  ctx += hoc"suc:i>i"
  ctx += hoc"z:i"
  ctx += hoc"E: nat>nat>o"
  ctx += hoc"LE: nat>nat>o"
  ctx += hoc"omega: nat>nat"
  ctx += hoc"phi: nat>nat"
  ctx += hoc"iLEQ:i>i>o"
  ctx += hoc"nu: nat>i>nat"
  ctx += hoc"chi: nat>i>nat"
  ctx += PrimRecFun( hoc"POR:nat>i>o", "POR 0 x = E 0 (f x) ", "POR (s y) x = (E (s y) (f x) ∨ POR y x)" )

  ctx += "LEDefinition" -> hos"POR(n,a) :- LE(f(a), s(n))"
  ctx += "LEDefinition2" -> hos"POR(n,suc(a)) :- LE(f(a), s(n))"
  ctx += "NumericTransitivity" -> hos"E(n,f(a)),E(n,f(suc(a))) :- E(f(a), f(suc(a)))"
  ctx += "minimalElement" -> hos"LE(f(z),0) :- "
  ctx += "reflexive" -> hos":- iLEQ(a,a)"
  ctx += "ordcon" -> hos"LE(f(a),s(n)) :- E(n,f(a)), LE(f(a),n)"
  ctx += "ordcon2" -> hos"LE(f(suc(a)),s(n)) :- E(n,f(suc(a))), LE(f(a),n)"

  val esOmega = Sequent(
    Seq( hof"!x POR(n,x)" ),
    Seq( hof"?z ( E(f(z), f(suc(z))) & ?x (  iLEQ(suc(z),suc(x)) & E(f(x), f(suc(x))) & ?y ( iLEQ(suc(x),suc(y)) & E(f(y), f(suc(y))) )))" ) )
  ctx += ProofNameDeclaration( le"omega n", esOmega )
  val esPhi = Sequent(
    Seq( hof"?x ( E(n,f(x)) & E(n,f(suc(x)))) | !y (LE(f(y),n))" ),
    Seq( hof"?z ( E(f(z), f(suc(z))) & ?x (  iLEQ(suc(z),suc(x)) & E(f(x), f(suc(x))) & ?y ( iLEQ(suc(x),suc(y)) & E(f(y), f(suc(y))) )))" ) )
  ctx += ProofNameDeclaration( le"phi n", esPhi )
  val esChi = Sequent(
    Seq( hof"?x ( iLEQ(suc(a),suc(x)) & E(n,f(x)) & E(n,f(suc(x)))) | !y (iLEQ(suc(a),suc(y)) & LE(f(y),n))" ),
    Seq( hof"?x (iLEQ(suc(a),suc(x)) & E(f(x), f(suc(x))) & ?y ( iLEQ(suc(x),suc(y)) & E(f(y), f(suc(y))) ))" ) )
  ctx += ProofNameDeclaration( le"chi n a", esChi )
  val esNu = Sequent(
    Seq( hof"?x ( iLEQ(suc(a),suc(x)) & E(n,f(x)) & E(n,f(suc(x)))) | !y (iLEQ(suc(a),suc(y)) & LE(f(y),n))" ),
    Seq( hof"?x ( iLEQ(suc(a),suc(x)) & E(f(x), f(suc(x))) )" ) )
  ctx += ProofNameDeclaration( le"nu n a", esNu )

  //The base case of  omega
  val esOmegaBc =
    Sequent(
      Seq( "Ant_0" -> hof"!x POR(0,x)" ),
      Seq( "Suc_0" -> hof"?z ( E(f(z), f(suc(z))) & ?x (  iLEQ(suc(z),suc(x)) & E(f(x), f(suc(x))) & ?y ( iLEQ(suc(x),suc(y)) & E(f(y), f(suc(y))) )))" ) )
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
  ctx += ProofDefinitionDeclaration( le"omega 0", omegaBc )

  val esOmegaSc =
    Sequent(
      Seq( "Ant_0" -> hof"!x POR(s(n),x)" ),
      Seq( "Suc_0" -> hof"?z ( E(f(z), f(suc(z))) & ?x (  iLEQ(suc(z),suc(x)) & E(f(x), f(suc(x))) & ?y ( iLEQ(suc(x),suc(y)) & E(f(y), f(suc(y))) )))" ) )
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
  ctx += ProofDefinitionDeclaration( le"omega (s n)", omegaSc )

  val esPhiBc =
    Sequent(
      Seq( "Ant_0" -> hof"?x ( E(0,f(x)) & E(0,f(suc(x)))) | !y (LE(f(y),0))" ),
      Seq( "Suc_0" -> hof"?z ( E(f(z), f(suc(z))) & ?x (  iLEQ(suc(z),suc(x)) & E(f(x), f(suc(x))) & ?y ( iLEQ(suc(x),suc(y)) & E(f(y), f(suc(y))) )))" ) )
  val phiBc = Lemma( esPhiBc ) {
    orL
    exL( fov"a" )
    andL
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
  ctx += ProofDefinitionDeclaration( le"phi 0", phiBc )

  val esPhiSc =
    Sequent(
      Seq( "Ant_0" -> hof"?x ( E(s(n),f(x)) & E(s(n),f(suc(x)))) | !y (LE(f(y),s(n)))" ),
      Seq( "Suc_0" -> hof"?z ( E(f(z), f(suc(z))) & ?x (  iLEQ(suc(z),suc(x)) & E(f(x), f(suc(x))) & ?y ( iLEQ(suc(x),suc(y)) & E(f(y), f(suc(y))) )))" ) )
  val phiSc = Lemma( esPhiSc ) {
    cut( "cut", hof"?x ( E(n,f(x)) & E(n,f(suc(x)))) | !y (LE(f(y),n))" )
    orR
    orL
    exL( fov"a" )
    andL
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
  ctx += ProofDefinitionDeclaration( le"phi (s n)", phiSc )

  val esChiBc =
    Sequent(
      Seq( "Ant_0" -> hof"?x (iLEQ(suc(a),suc(x)) & E(0,f(x)) & E(0,f(suc(x)))) | !y (iLEQ(suc(a),suc(y)) & LE(f(y),0))" ),
      Seq( "Suc_0" -> hof"?x ( iLEQ(suc(a),suc(x)) & E(f(x), f(suc(x))) & ?y ( iLEQ(suc(x),suc(y)) & E(f(y), f(suc(y))) ))" ) )
  val chiBc = Lemma( esChiBc ) {
    orL
    exL( fov"b" )
    andL
    andL
    exR( fov"b" )
    andR
    andR
    trivial
    ref( "NumericTransitivity" )
    cut( "cut2", hof"?x (iLEQ(suc(b),suc(x)) & E(0,f(x)) & E(0,f(suc(x)))) | !y (iLEQ(suc(b),suc(y))  & LE(f(y),0))" )
    orR
    exR( "cut2_0", fov"b" )
    andR
    andR
    ref( "reflexive" )
    trivial
    trivial
    ref( "nu" )
    allL( foc"z" )
    andL
    ref( "minimalElement" )
  }
  ctx += ProofDefinitionDeclaration( le"chi 0 a", chiBc )

  val esChiSc =
    Sequent(
      Seq( "Ant_0" -> hof"?x (  iLEQ(suc(a),suc(x)) & E(s(n),f(x)) & E(s(n),f(suc(x)))) | !y (iLEQ(suc(a),suc(y)) & LE(f(y),s(n)))" ),
      Seq( "Suc_0" -> hof"?x ( iLEQ(suc(a),suc(x)) & E(f(x), f(suc(x))) & ?y ( iLEQ(suc(x),suc(y)) & E(f(y), f(suc(y))) ))" ) )
  val chiSc = Lemma( esChiSc ) {
    cut( "cut", hof"?x ( iLEQ(suc(a),suc(x)) & E(n,f(x)) & E(n,f(suc(x)))) | !y (iLEQ(suc(a),suc(y))& LE(f(y),n))" )
    orR
    orL
    exL( fov"b" )
    andL
    andL
    exR( "Suc_0", fov"b" )
    andR
    andR
    trivial
    ref( "NumericTransitivity" )
    cut( "cut2", hof"?x (iLEQ(suc(b),suc(x)) & E(s(n),f(x)) & E(s(n),f(suc(x)))) | !y (iLEQ(suc(b),suc(y)) & LE(f(y),s(n)))" )
    orR
    exR( "cut2_0", fov"b" )
    andR
    andR
    ref( "reflexive" )
    trivial
    trivial
    ref( "nu" )
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
  ctx += ProofDefinitionDeclaration( le"chi (s n) a", chiSc )

  val esNuBc =
    Sequent(
      Seq( "Ant_0" -> hof"?x (iLEQ(suc(a),suc(x)) & E(0,f(x)) & E(0,f(suc(x)))) | !y (iLEQ(suc(a),suc(y)) & LE(f(y),0))" ),
      Seq( "Suc_0" -> hof"?x ( iLEQ(suc(a),suc(x)) & E(f(x), f(suc(x))) )" ) )
  val nuBc = Lemma( esNuBc ) {
    orL
    exL( fov"b" )
    andL
    andL
    exR( fov"b" )
    andR
    trivial
    ref( "NumericTransitivity" )
    allL( foc"z" )
    andL
    ref( "minimalElement" )
  }
  ctx += ProofDefinitionDeclaration( le"nu 0 a", nuBc )

  val esNuSc =
    Sequent(
      Seq( "Ant_0" -> hof"?x (  iLEQ(suc(a),suc(x)) & E(s(n),f(x)) & E(s(n),f(suc(x)))) | !y (iLEQ(suc(a),suc(y)) & LE(f(y),s(n)))" ),
      Seq( "Suc_0" -> hof"?x (  iLEQ(suc(a),suc(x)) & E(f(x), f(suc(x))) )" ) )
  val nuSc = Lemma( esNuSc ) {
    cut( "cut", hof"?x ( iLEQ(suc(a),suc(x)) & E(n,f(x)) & E(n,f(suc(x)))) | !y (iLEQ(suc(a),suc(y)) & LE(f(y),n))" )
    orR
    orL
    exL( fov"b" )
    andL
    andL
    exR( "Suc_0", fov"b" )
    andR
    trivial
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
    ref( "nu" )
  }
  ctx += ProofDefinitionDeclaration( le"nu (s n) a", nuSc )
}

