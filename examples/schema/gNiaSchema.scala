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

//val two = LKProofSchemata.Instantiate("omega",Seq(le"((s:w>w) (0:w))",le"(0:w)"))(gniaSchema.ctx)

object gniaSchema extends TacticsProof {
  ctx += InductiveType( "nat", hoc"0 : nat", hoc"s : nat>nat" )
  ctx += Sort( "i" )
  ctx += hoc"f:i>nat"
  ctx += hoc"E: nat>nat>o"
  ctx += hoc"LE: i>i>o"
  ctx += PrimRecFun( hoc"POR:nat>i>o", "POR 0 x = E (f x) 0", "POR (s y) x = (E (f x) (s y) ∨ POR y x)" )
  ctx += PrimRecFun( hoc"Ech:nat>i>o", "Ech 0 x = (∃p ((LE x p) ∧  (E (f x) (f p))))", "Ech (s y) x = (∃p ((Ech y p) ∧ (LE x p) ∧  (E (f x) (f p))))" )
  ctx += hoc"LEQ: i>i>o"
  ctx += hoc"z:i"
  ctx += hoc"g:i>i"
  ctx += hoc"max:i>i>i"
  ctx += hoc"mu: nat>nat>nat"
  ctx += hoc"mubase: nat>nat"
  ctx += hoc"nu: nat>nat>i>nat"
  ctx += hoc"nuPrime:nat>i>nat"
  ctx += hoc"omega: nat>nat>nat"
  ctx += hoc"phi: nat>nat>nat"
  ctx += hoc"chi: nat>i>nat"
  ctx += "efef" -> hcl"E(f(p),n),E(f(q),n) :- E(f(p),f(q))"
  ctx += "leq_refl" -> hos" :- LEQ(p,p)"
  ctx += "leq_g" -> hos"LEQ(g(p),q):- LE(p,q)"
  ctx += "leq_max1" -> hos"LEQ(max(a, b), c) :- LEQ(a, c)"
  ctx += "leq_max2" -> hos"LEQ(max(a, b), c) :- LEQ(b, c)"

  //Schematic Definitions

  //The Name declaration of proof nu
  val esnu = Sequent(
    Seq(
      hof"E(f(A),n)",
      hof"!x?y(LEQ(x,y) & E(f(y),n))" ),
    Seq( hof"Ech(m,A)" ) )

  ctx += ProofNameDeclaration( le"nu m n A", esnu )

  //The Name declaration of proof mu
  val esmu = Sequent(
    Seq(
      hof"!x?y(LEQ(x,y) & E(f(y),n))" ),
    Seq( hof"?p Ech(m,p)" ) )

  ctx += ProofNameDeclaration( le"mu m n", esmu )

  //The Name declaration of proof mubase
  val esmubase = Sequent(
    Seq(
      hof"!x?y(LEQ(x,y) & E(f(y),0))" ),
    Seq( hof"?p Ech(m,p)" ) )

  ctx += ProofNameDeclaration( le"mubase m", esmubase )

  //The Name declaration of proof chi
  val eschi = Sequent(
    Seq(
      hof" POR(n,a) " ),
    Seq( hof"POR(n,a)" ) )
  ctx += ProofNameDeclaration( le"chi n a", eschi )
  //The Name declaration of proof nuPrime
  val esnuPrime = Sequent(
    Seq(
      hof"E(f(A),0)",
      hof"!x?y(LEQ(x,y) & POR(0,y))" ),
    Seq( hof"Ech(m,A)" ) )

  ctx += ProofNameDeclaration( le"nuPrime m A", esnuPrime )

  //The Name declaration of proof omega
  val esOmega = Sequent(
    Seq(
      hof"!x POR(n,x)" ),
    Seq( hof"?p Ech(m,p)" ) )
  ctx += ProofNameDeclaration( le"omega n m", esOmega )

  //The Name declaration of proof phi
  val esphi = Sequent(
    Seq(
      hof"!x?y (LEQ(x,y) & POR(n,y) )" ),
    Seq( hof"?p Ech(m,p)" ) )
  ctx += ProofNameDeclaration( le"phi n m", esphi )
  //The base case of  mubase
  val esMubaseBc = Sequent(
    Seq(
      ( "Ant_2" -> hof"!x?y(LEQ(x,y) & E(f(y),0))" ) ),
    Seq( ( "Suc_0" -> hof"?q Ech(0,q)" ) ) )
  val mubaseBc = Lemma( esMubaseBc ) {
    allL( "Ant_2", hoc"z:i" )
    exL( fov"B" )
    allL( "Ant_2", le"(g B)" )
    exL( fov"A" )
    exR( fov"B" )
    unfold( "Ech" ) atMost 1 in "Suc_0_0"
    exR( "Suc_0_0", fov"A" )
    andL( "Ant_2_1" )
    andL
    andR onAll foTheory
  }
  ctx += ProofDefinitionDeclaration( le"mubase 0", mubaseBc )

  //The step case of  mu
  val esMubaseSc = Sequent(
    Seq(
      ( "Ant_2" -> hof"!x?y(LEQ(x,y) & E(f(y),0))" ) ),
    Seq( ( "Suc_0" -> hof"?q Ech(s(m),q)" ) ) )
  val mubaseSc = Lemma( esMubaseSc ) {
    allL( "Ant_2", hoc"z:i" )
    exL( fov"B" )
    allL( "Ant_2", le"(g B)" )
    exL( fov"A" )
    exR( fov"B" )
    unfold( "Ech" ) atMost 1 in "Suc_0_0"
    exR( "Suc_0_0", fov"A" )
    andL( "Ant_2_1" )
    andL
    andR right foTheory
    andR right foTheory
    ref( "nu" )
  }
  ctx += ProofDefinitionDeclaration( le"mubase (s m)", mubaseSc )
  //The base case of  nu
  val esNuBc = Sequent(
    Seq(
      ( "Ant_2" -> hof"E(f(A),n)" ),
      ( "Ant_3" -> hof"!x?y(LEQ(x,y) & E(f(y),n))" ) ),
    Seq( ( "Suc_0" -> hof"Ech(0,A)" ) ) )
  val NuBc = Lemma( esNuBc ) {
    allL( "Ant_3", le"g(A)" )
    unfold( "Ech" ) atMost 1 in "Suc_0"
    exL( fov"B" )
    exR( fov"B" )
    andL
    andR onAll foTheory
  }
  ctx += ProofDefinitionDeclaration( le"nu 0 n A", NuBc )

  //The step case of  nu
  val esNuSc = Sequent(
    Seq(
      ( "Ant_2" -> hof"E(f(A),n)" ),
      ( "Ant_3" -> hof"!x?y(LEQ(x,y) & E(f(y),n))" ) ),
    Seq( ( "Suc_0" -> hof"Ech(s(m),A)" ) ) )
  val NuSc = Lemma( esNuSc ) {
    allL( "Ant_3", le"g(A)" )
    unfold( "Ech" ) atMost 1 in "Suc_0"
    exL( fov"B" )
    exR( fov"B" )
    andL
    andR right foTheory
    andR right foTheory
    ref( "nu" )
  }
  ctx += ProofDefinitionDeclaration( le"nu (s m) n  A", NuSc )

  //The base case of  nuPrime
  val esNuPrimeBc = Sequent(
    Seq(
      ( "Ant_2" -> hof"E(f(A),0)" ),
      ( "Ant_3" -> hof"!x?y(LEQ(x,y) & POR(0,y))" ) ),
    Seq( ( "Suc_0" -> hof"Ech(0,A)" ) ) )
  val NuPrimeBc = Lemma( esNuPrimeBc ) {
    allL( "Ant_3", le"g(A)" )
    unfold( "Ech" ) atMost 1 in "Suc_0"
    exL( fov"B" )
    exR( fov"B" )
    andL
    andR left foTheory
    unfold( "POR" ) atMost 1 in "Ant_3_0_1"
    foTheory
  }
  ctx += ProofDefinitionDeclaration( le"nuPrime 0 A", NuPrimeBc )

  //The step case of  nuPrime
  val esNuPrimeSc = Sequent(
    Seq(
      ( "Ant_2" -> hof"E(f(A),0)" ),
      ( "Ant_3" -> hof"!x?y(LEQ(x,y) & POR(0,y))" ) ),
    Seq( ( "Suc_0" -> hof"Ech(s(m),A)" ) ) )
  val NuPrimeSc = Lemma( esNuPrimeSc ) {
    allL( "Ant_3", le"g(A)" )
    unfold( "Ech" ) atMost 1 in "Suc_0"
    exL( fov"B" )
    exR( fov"B" )
    andL
    unfold( "POR" ) atMost 1 in "Ant_3_0_1"
    andR right foTheory
    andR right foTheory
    ref( "nuPrime" )
  }
  ctx += ProofDefinitionDeclaration( le"nuPrime (s m) A", NuPrimeSc )

  //The base case of  mu
  val esMuBc = Sequent(
    Seq(
      ( "Ant_2" -> hof"!x?y(LEQ(x,y) & E(f(y),n))" ) ),
    Seq( ( "Suc_0" -> hof"?q Ech(0,q)" ) ) )
  val muBc = Lemma( esMuBc ) {
    allL( "Ant_2", hoc"z:i" )
    exL( fov"B" )
    allL( "Ant_2", le"(g B)" )
    exL( fov"A" )
    exR( fov"B" )
    unfold( "Ech" ) atMost 1 in "Suc_0_0"
    exR( "Suc_0_0", fov"A" )
    andL( "Ant_2_1" )
    andL
    andR onAll foTheory
  }
  ctx += ProofDefinitionDeclaration( le"mu 0 n", muBc )

  //The step case of  mu
  val esMuSc = Sequent(
    Seq(
      ( "Ant_2" -> hof"!x?y(LEQ(x,y) & E(f(y),n))" ) ),
    Seq( ( "Suc_0" -> hof"?q Ech(s(m),q)" ) ) )
  val muSc = Lemma( esMuSc ) {
    allL( "Ant_2", hoc"z:i" )
    exL( fov"B" )
    allL( "Ant_2", le"(g B)" )
    exL( fov"A" )
    exR( fov"B" )
    unfold( "Ech" ) atMost 1 in "Suc_0_0"
    exR( "Suc_0_0", fov"A" )
    andL( "Ant_2_1" )
    andL
    andR right foTheory
    andR right foTheory
    ref( "nu" )
  }
  ctx += ProofDefinitionDeclaration( le"mu (s m) n ", muSc )

  // The Basecase of chi
  val esChiBc = Sequent(
    Seq(
      ( "Ant_2" -> hof" POR(0,a)" ) ),
    Seq(
      ( "Suc_0" -> hof"POR(0,a)" ) ) )
  val chiBc = Lemma( esChiBc ) {
    unfold( "POR" ) atMost 1 in "Suc_0"
    unfold( "POR" ) atMost 1 in "Ant_2"
    trivial
  }
  ctx += ProofDefinitionDeclaration( le"chi 0 a", chiBc )

  //The step case of chi
  val esChiSc = Sequent(
    Seq(
      ( "Ant_2" -> hof" POR(s(n),a)" ) ),
    Seq(
      ( "Suc_0" -> hof"POR(s(n),a)" ) ) )
  val chiSc = Lemma( esChiSc ) {
    unfold( "POR" ) atMost 1 in "Suc_0"
    unfold( "POR" ) atMost 1 in "Ant_2"
    orR
    orL left trivial
    ref( "chi" )
  }
  ctx += ProofDefinitionDeclaration( le"chi (s n) a", chiSc )

  //The base case of phi
  val esphiBc = Sequent(
    Seq(
      ( "Ant_2" -> hof"!x?y (LEQ(x,y) & POR(0,y))" ) ),
    Seq( ( "Suc_0" -> hof"?p Ech(m,p)" ) ) )
  val phiBc = Lemma( esphiBc ) {
    allL( "Ant_2", hoc"z:i" )
    exL( fov"B" )
    allL( "Ant_2", le"(g B)" )
    exL( fov"A" )
    exR( fov"A" )
    andL( "Ant_2_1" )
    unfold( "POR" ) atMost 1 in "Ant_2_1_1"
    ref( "nuPrime" )
  }
  ctx += ProofDefinitionDeclaration( le"phi 0 m", phiBc )

  //The step case of phi

  val esphiSc = Sequent(
    Seq(
      "Ant_2" -> hof"!x?y (LEQ(x,y) & POR(s(n),y))" ),
    Seq( "Suc_0" -> hof"?p Ech(m,p)" ) )
  val phiSc = Lemma( esphiSc ) {
    cut( "cut", hof"!x?y (LEQ(x,y) & E(f(y),s(n)))" ) right ref( "mu" )
    cut( "cut1", hof"!x?y (LEQ(x,y) & POR(n,y))" ) right ref( "phi" )
    allR( "cut", fov"B" )
    allR( "cut1", fov"A" )
    allL( "Ant_2", le"max(A,B)" )
    exL( "Ant_2_0", fov"C" )
    exR( "cut", fov"C" )
    exR( "cut1", fov"C" )
    andL
    andR( "cut_0" ) left by {
      andR( "cut1_0" ) onAll foTheory
    }
    unfold( "POR" ) atMost 1 in "Ant_2_0_1"
    orL left trivial
    andR( "cut1_0" ) left foTheory
    ref( "chi" )
  }
  ctx += ProofDefinitionDeclaration( le"phi (s n) m", phiSc )

  //The base case of  omega
  val esOmegaBc = Sequent(
    Seq(
      ( "Ant_2" -> hof"!x POR(0,x)" ) ),
    Seq( ( "Suc_0" -> hof"?p Ech(m,p)" ) ) )
  val omegaBc = Lemma( esOmegaBc ) {
    cut( "cut", hof"!x?y (LEQ(x,y) & E(f(y),0))" ) right ref( "mubase" )
    allR( fov"A" )
    allL( "Ant_2", fov"A" )
    exR( "cut", fov"A" )
    unfold( "POR" ) atMost 1 in "Ant_2_0"
    andR; foTheory; trivial
  }
  ctx += ProofDefinitionDeclaration( le"omega 0 m", omegaBc )

  //The Step case of  omega
  val esOmegaSc = Sequent(
    Seq(
      ( "Ant_2" -> hof"!x POR(s(n),x)" ) ),
    Seq( ( "Suc_0" -> hof"?p Ech(m,p)" ) ) )
  val omegaSc = Lemma( esOmegaSc ) {
    cut( "cut", hof"!x?y (LEQ(x,y) & POR(s(n),y))" ) right ref( "phi" )
    allR( fov"A" )
    allL( "Ant_2", fov"A" )
    exR( "cut", fov"A" )
    andR left foTheory
    ref( "chi" )
  }
  ctx += ProofDefinitionDeclaration( le"omega (s n) m", omegaSc )
}

