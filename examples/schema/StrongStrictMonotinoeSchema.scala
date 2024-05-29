package gapt.examples

import gapt.expr._
import gapt.proofs.Sequent
import gapt.proofs.context.update.InductiveType
import gapt.proofs.context.update.{PrimitiveRecursiveFunction => PrimRecFun}
import gapt.proofs.context.update.ProofDefinitionDeclaration
import gapt.proofs.context.update.ProofNameDeclaration
import gapt.proofs.context.update.Sort
import gapt.proofs.gaptic._

object StrongStrictMonotoneSchema extends TacticsProof {
  ctx += InductiveType("nat", hoc"0 : nat", hoc"s : nat>nat")
  ctx += Sort("i")
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
  ctx += PrimRecFun(hoc"POR:nat>i>o", "POR 0 x = E 0 (f x) ", "POR (s y) x = (E (s y) (f x) ∨ POR y x)")
  ctx += "LEDefinition" -> hos"POR(n,a) :- LE(f(a), s(n))"
  ctx += "NumericTransitivity" -> hos"E(n,f(a)),E(n,f(suc(a))) :- E(f(a), f(suc(a)))"
  ctx += "minimalElement" -> hos"LE(n,0) :- "
  ctx += "reflexivity" -> hos" :- iLEQ(a,a)"
  ctx += "SucDef" -> hos":- iLEQ(a,suc(a))"
  ctx += "ordcon" -> hos"LE(f(a),s(n)),iLEQ(a,b) :- E(n,f(b)), LE(f(b),n)"

  val esOmega = Sequent(
    Seq(hof"!x POR(n,x)"),
    Seq(hof"?x ( E(f(x), f(suc(x))) )")
  )
  ctx += ProofNameDeclaration(le"omega n", esOmega)
  val esPhi = Sequent(
    Seq(hof"?x !y ((iLEQ(x,y) -> E(n,f(y))) | LE(f(y),n))"),
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
    cut("cut", hof"?x !y ((iLEQ(x,y) -> E(0,f(y))) | LE(f(y),0))")
    exR("cut", hoc"z")
    allR("cut_0", fov"a")
    orR
    impR
    allL("Ant_0", fov"a")
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
    cut("cut", hof"?x !y ((iLEQ(x,y) -> E(s(n),f(y))) | LE(f(y),s(n)))")
    exR("cut", hoc"z")
    allR("cut_0", fov"a")
    orR
    impR
    allL("Ant_0", fov"a")
    unfold("POR") atMost 1 in "Ant_0_0"
    orL
    trivial
    ref("LEDefinition")
    ref("phi")

  }
  ctx += ProofDefinitionDeclaration(le"omega (s n)", omegaSc)

  val esPhiBc =
    Sequent(
      Seq("Ant_0" -> hof"?x !y ((iLEQ(x,y) -> E(0,f(y))) | LE(f(y),0))"),
      Seq("Suc_0" -> hof"?x (E(f(x), f(suc(x))) )")
    )
  val phiBc = Lemma(esPhiBc) {
    exL(fov"a")
    allL(fov"a")
    allL(le"(suc a)")
    exR(fov"a")
    orL("Ant_0_0")
    orL("Ant_0_1")
    impL("Ant_0_0")
    impL("Ant_0_1")
    ref("SucDef")
    ref("reflexivity")
    impL("Ant_0_1")
    ref("SucDef")
    ref("NumericTransitivity")
    ref("minimalElement")
    ref("minimalElement")
  }
  ctx += ProofDefinitionDeclaration(le"phi 0", phiBc)

  val esPhiSc =
    Sequent(
      Seq("Ant_0" -> hof"?x !y ((iLEQ(x,y) -> E(s(n),f(y))) | LE(f(y),s(n)))"),
      Seq("Suc_0" -> hof"?x (E(f(x), f(suc(x))) )")
    )
  val phiSc = Lemma(esPhiSc) {
    cut("cut", hof"?x !y ((iLEQ(x,y) -> E(n,f(y))) | LE(f(y),n))")
    exL(fov"a")
    exR("cut", fov"a")
    exR("cut", le"(suc a)")
    allL(fov"a")
    allR("cut_0", fov"b")
    orR
    impR
    orL
    focus(1)
    ref("ordcon")
    impL
    ref("reflexivity")
    allR("cut_1", fov"c")
    orR
    impR
    allL(le"suc(a)")
    orL
    focus(1)
    ref("ordcon")
    impL
    ref("SucDef")
    focus(1)
    ref("phi")
    exR("Suc_0", fov"a")
    ref("NumericTransitivity")
  }
  ctx += ProofDefinitionDeclaration(le"phi (s n)", phiSc)

}
