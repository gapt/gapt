package gapt.examples

import gapt.expr._
import gapt.proofs.Sequent
import gapt.proofs.context.Context
import gapt.proofs.context.update.InductiveType
import gapt.proofs.context.update.{ PrimitiveRecursiveFunction => PrimRecFun }
import gapt.proofs.context.update.ProofDefinitionDeclaration
import gapt.proofs.context.update.ProofNameDeclaration
import gapt.proofs.context.update.Sort
import gapt.proofs.gaptic._

object NiaSchema extends TacticsProof {
  ctx += InductiveType( "nat", hoc"0 : nat", hoc"s : nat>nat" )
  ctx += Sort( "i" )
  ctx += hoc"f:i>nat"
  ctx += hoc"E: nat>nat>o"
  ctx += hoc"LEQ: i>i>o"
  ctx += hoc"LE: i>i>o"
  ctx += PrimRecFun( hoc"POR:nat>i>o", "POR 0 x = E (f x) 0", "POR (s y) x = (E (f x) (s y) ∨ POR y x)" )

  ctx += hoc"z:i" //This is the Zero for the Iota sort
  ctx += hoc"g:i>i" //This is the Successor for the Iota sort
  ctx += hoc"max:i>i>i"
  ctx += hoc"omega: nat>nat"
  ctx += hoc"phi: nat>nat"
  ctx += hoc"chi: nat>i>nat"
  ctx += "efef" -> hos"E(f(p),n),E(f(q),n) :- E(f(p),f(q))"
  ctx += "leq_refl" -> hos" :- LEQ(p,p)"
  ctx += "leq_g" -> hos"LEQ(g(p),q):- LE(p,q)"
  ctx += "leq_max1" -> hos"LEQ(max(a, b), c) :- LEQ(a, c)"
  ctx += "leq_max2" -> hos"LEQ(max(a, b), c) :- LEQ(b, c)"

  //The Name declaration of proof omega
  val esOmega = Sequent(
    Seq( hof"!x POR(n,x)" ),
    Seq( hof"?p?q (LE(p,q) & E(f(p),f(q)))" ) )
  ctx += ProofNameDeclaration( le"omega n", esOmega )
  //The Name declaration of proof phi
  val esphi = Sequent(
    Seq( hof"!x?y (LEQ(x,y) & POR(n,y) )" ),
    Seq( hof"?p?q (LE(p,q) & E(f(p),f(q)))" ) )
  ctx += ProofNameDeclaration( le"phi n", esphi )
  //The Name declaration of proof chi
  val eschi = Sequent(
    Seq( hof" POR(n,a) " ),
    Seq( hof"POR(n,a)" ) )
  ctx += ProofNameDeclaration( le"chi n a", eschi )

  //The base case of  omega
  val esOmegaBc = Sequent(
    Seq( "Ant_2" -> hof"!x POR(0,x)" ),
    Seq( "Suc_0" -> hof"?p?q (LE(p,q) & E(f(p),f(q))) " ) )
  val omegaBc = Lemma( esOmegaBc ) {
    cut( "cut", hof"!x?y (LEQ(x,y) & E(f(y),0))" )
    allR( fov"A" )
    allL( "Ant_2", fov"A" )
    exR( "cut", fov"A" )
    unfold( "POR" ) atMost 1 in "Ant_2_0"
    andR
    foTheory
    trivial
    forget( "Ant_2" )
    allL( hoc"z:i" )
    exL( fov"B" )
    allL( le"(g B)" )
    exL( fov"A" )
    exR( fov"B" )
    forget( "Suc_0" )
    exR( fov"A" )
    forget( "Suc_0_0" )
    andL( "cut_1" )
    andL
    andR
    foTheory
    foTheory
  }
  ctx += ProofDefinitionDeclaration( le"omega 0", omegaBc )

  //The Step case of  omega
  //Need to complete
  val esOmegaSc = Sequent(
    Seq( "Ant_2" -> hof"!x POR(s(n),x)" ),
    Seq( "Suc_0" -> hof"?p?q (LE(p,q) & E(f(p),f(q))) " ) )
  val omegaSc = Lemma( esOmegaSc ) {
    cut( "cut", hof"!x?y (LEQ(x,y) & POR(s(n),y))" )
    allR( fov"A" )
    allL( "Ant_2", fov"A" )
    exR( "cut", fov"A" )
    andR
    foTheory
    ref( "chi" )
    ref( "phi" )
  }
  ctx += ProofDefinitionDeclaration( le"omega (s n)", omegaSc )

  // The Basecase of chi
  val esChiBc = Sequent(
    Seq(
      "Ant_2" -> hof" POR(0,a)" ),
    Seq(
      "Suc_0" -> hof"POR(0,a)" ) )
  val chiBc = Lemma( esChiBc ) {
    unfold( "POR" ) atMost 1 in "Suc_0"
    unfold( "POR" ) atMost 1 in "Ant_2"
    trivial
  }
  ctx += ProofDefinitionDeclaration( le"chi 0 a", chiBc )

  //The step case of chi
  val esChiSc = Sequent(
    Seq(
      "Ant_2" -> hof" POR(s(n),a)" ),
    Seq(
      "Suc_0" -> hof"POR(s(n),a)" ) )
  val chiSc = Lemma( esChiSc ) {
    unfold( "POR" ) atMost 1 in "Suc_0"
    unfold( "POR" ) atMost 1 in "Ant_2"
    orR
    orL
    trivial
    ref( "chi" )
  }
  ctx += ProofDefinitionDeclaration( le"chi (s n) a", chiSc )

  //The base case of phi
  val esphiBc = Sequent(
    Seq(
      "Ant_2" -> hof"!x?y (LEQ(x,y) & POR(0,y))" ),
    Seq( "Suc_0" -> hof"?p?q (LE(p,q) & E(f(p),f(q))) " ) )
  val phiBc = Lemma( esphiBc ) {
    allL( "Ant_2", hoc"z:i" )
    exL( fov"B" )
    allL( "Ant_2", le"(g B)" )
    exL( fov"A" )
    exR( fov"B" )
    forget( "Suc_0" )
    exR( fov"A" )
    forget( "Suc_0_0" )
    andL( "Ant_2_1" )
    andL
    andR
    foTheory
    unfold( "POR" ) atMost 1 in "Ant_2_0_1"
    unfold( "POR" ) atMost 1 in "Ant_2_1_1"
    foTheory
  }
  ctx += ProofDefinitionDeclaration( le"phi 0", phiBc )

  //The step case of phi

  val esphiSc = Sequent(
    Seq(
      "Ant_2" -> hof"!x?y (LEQ(x,y) & POR(s(n),y))" ),
    Seq( "Suc_0" -> hof"?p?q (LE(p,q) & E(f(p),f(q)))" ) )
  val phiSc = Lemma( esphiSc ) {
    cut( "cut", hof"!x?y (LEQ(x,y) & E(f(y),s(n)))" )
    cut( "cut1", hof"!x?y (LEQ(x,y) & POR(n,y))" )
    allR( "cut", fov"B" )
    allR( "cut1", fov"A" )
    allL( "Ant_2", le"max(A,B)" )
    exL( "Ant_2_0", fov"C" )
    exR( "cut", fov"C" )
    exR( "cut1", fov"C" )
    andL
    andR( "cut_0" )
    andR( "cut1_0" )
    foTheory
    foTheory
    unfold( "POR" ) atMost 1 in "Ant_2_0_1"
    orL
    trivial
    andR( "cut1_0" )
    foTheory
    forget( "Ant_2_0_0" )
    forget( "Ant_2" )
    forget( "Suc_0" )
    forget( "cut" )
    forget( "cut1" )
    forget( "cut_0" )
    ref( "chi" )
    focus( 1 )
    forget( "Ant_2" )
    allL( hoc"z:i" )
    exL( fov"B" )
    allL( le"(g B)" )
    exL( fov"A" )
    exR( fov"B" )
    forget( "Suc_0" )
    exR( fov"A" )
    forget( "Suc_0_0" )
    andL( "cut_1" )
    andL
    andR
    foTheory
    foTheory
    ref( "phi" )
  }
  ctx += ProofDefinitionDeclaration( le"phi (s n)", phiSc )
}

