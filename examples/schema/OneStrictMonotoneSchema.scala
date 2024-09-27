package gapt.examples

import gapt.expr._
import gapt.proofs.Sequent
import gapt.proofs.context.update.InductiveType
import gapt.proofs.context.update.{PrimitiveRecursiveFunction => PrimRecFun}
import gapt.proofs.context.update.ProofDefinitionDeclaration
import gapt.proofs.context.update.ProofNameDeclaration
import gapt.proofs.context.update.Sort
import gapt.proofs.gaptic._

object OneStrictMonotoneSchema extends TacticsProof {
  ctx += InductiveType("nat", hoc"0 : nat", hoc"s : nat>nat")
  ctx += Sort("i")
  ctx += hoc"f:i>nat"
  ctx += hoc"suc:i>i"
  ctx += hoc"z:i"
  ctx += hoc"E: nat>nat>o"
  ctx += hoc"LE: nat>nat>o"

  ctx += hoc"omega: nat>nat"
  ctx += hoc"phi: nat>nat"
  ctx += PrimRecFun(hoc"POR:nat>i>o", "POR 0 x = E 0 (f x) ", "POR (s y) x = (E (s y) (f x) ∨ POR y x)")
  ctx += "LEDefinition" -> hos"POR(n,a) :- LE(f(a), s(n))"
  ctx += "LEDefinition2" -> hos"POR(n,suc(a)) :- LE(f(a), s(n))"
  ctx += "NumericTransitivity" -> hos"E(n,f(a)),E(n,f(suc(a))) :- E(f(a), f(suc(a)))"
  ctx += "minimalElement" -> hos"LE(f(z),0) :- "
  ctx += "ordcon" -> hos"LE(f(a),s(n)) :- E(n,f(a)), LE(f(a),n)"
  ctx += "ordcon2" -> hos"LE(f(suc(a)),s(n)) :- E(n,f(suc(a))), LE(f(a),n)"

  val esOmega = Sequent(
    Seq(hof"!x POR(n,x)"),
    Seq(hof"?x ( E(f(x), f(suc(x))) )")
  )
  ctx += ProofNameDeclaration(le"omega n", esOmega)
  val esPhi = Sequent(
    Seq(hof"?x ( E(n,f(x)) & E(n,f(suc(x)))) | !y (LE(f(y),n))"),
    Seq(hof"?x ( E(f(x), f(suc(x))) )")
  )
  ctx += ProofNameDeclaration(le"phi n", esPhi)

  // The base case of  omega
  val esOmegaBc =
    Sequent(
      Seq("Ant_0" -> hof"!x POR(0,x)"),
      Seq("Suc_0" -> hof"?x (E(f(x), f(suc(x))))")
    )
  val omegaBc = Lemma(esOmegaBc) {
    cut("cut", hof"?x ( E(0,f(x)) & E(0,f(suc(x)))) | !y (LE(f(y),0))")
    orR
    exR("cut_0", hoc"z")
    andR
    allL("Ant_0", hoc"z")
    unfold("POR") atMost 1 in "Ant_0_0"
    trivial
    allL("Ant_0", le"(suc z)")
    unfold("POR") atMost 1 in "Ant_0_0"
    trivial
    ref("phi")
  }
  ctx += ProofDefinitionDeclaration(le"omega 0", omegaBc)
  val esOmegaSc =
    Sequent(
      Seq("Ant_0" -> hof"!x POR(s(n),x)"),
      Seq("Suc_0" -> hof"?x (E(f(x), f(suc(x))))")
    )
  val omegaSc = Lemma(esOmegaSc) {
    cut("cut", hof"?x ( E(s(n),f(x)) & E(s(n),f(suc(x)))) | !y (LE(f(y),s(n)))")
    orR
    allR("cut_1", fov"a")
    exR("cut_0", fov"a")
    andR
    allL("Ant_0", fov"a")
    unfold("POR") atMost 1 in "Ant_0_0"
    orL
    trivial
    ref("LEDefinition")
    allL("Ant_0", le"(suc a)")
    unfold("POR") atMost 1 in "Ant_0_0"
    orL
    trivial
    ref("LEDefinition2")
    ref("phi")

  }
  ctx += ProofDefinitionDeclaration(le"omega (s n)", omegaSc)

  val esPhiBc =
    Sequent(
      Seq("Ant_0" -> hof"?x ( E(0,f(x)) & E(0,f(suc(x)))) | !y (LE(f(y),0))"),
      Seq("Suc_0" -> hof"?x (E(f(x), f(suc(x))) )")
    )
  val phiBc = Lemma(esPhiBc) {
    orL
    exL(fov"a")
    andL
    exR(fov"a")
    ref("NumericTransitivity")
    allL(foc"z")
    ref("minimalElement")
  }
  ctx += ProofDefinitionDeclaration(le"phi 0", phiBc)

  val esPhiSc =
    Sequent(
      Seq("Ant_0" -> hof"?x ( E(s(n),f(x)) & E(s(n),f(suc(x)))) | !y (LE(f(y),s(n)))"),
      Seq("Suc_0" -> hof"?x (E(f(x), f(suc(x))) )")
    )
  val phiSc = Lemma(esPhiSc) {
    cut("cut", hof"?x ( E(n,f(x)) & E(n,f(suc(x)))) | !y (LE(f(y),n))")
    orR
    orL
    exL(fov"a")
    andL
    exR("Suc_0", fov"a")
    ref("NumericTransitivity")
    allR(fov"b")
    exR("cut_0", fov"b")
    allL(fov"b")
    andR
    ref("ordcon")
    allL(le"(suc b)")
    ref("ordcon2")
    ref("phi")
  }
  ctx += ProofDefinitionDeclaration(le"phi (s n)", phiSc)

}
