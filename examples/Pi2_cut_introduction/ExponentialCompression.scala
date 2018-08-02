package gapt.examples

import gapt.expr._
import gapt.proofs.Context._
import gapt.proofs.gaptic._
import gapt.proofs.Context
import gapt.proofs.Sequent

object ExponentialCompression extends TacticsProof {

  ctx += Context.InductiveType( "nat", hoc"0 : nat", hoc"s : nat>nat" )
  ctx += Context.Sort( "i" )

  ctx += hoc"a:i"
  ctx += hoc"f:i>i"
  ctx += hoc"g:i>i"
  ctx += hoc"fn:nat>i>i"

  ctx += hoc"chi: nat>nat"
  ctx += hoc"phi: nat>i>nat"
  ctx += hoc"xhi: nat>i>i>nat"

  ctx += hoc"P: i>i>o"

  ctx += PrimRecFun(
    hoc"Disjunction: nat>i>o",
    "( Disjunction 0 x ) = ( ( P x ( fn 0 x ) ) ∨ ( P x ( fn (s 0) x ) ) )",
    "( Disjunction (s xn) x ) = ( ( Disjunction xn x ) ∨ ( P x ( fn (s xn) x ) ) )" )
  ctx += PrimRecFun(
    hoc"Conjunction: nat>i>i>o",
    "( Conjunction 0 x y ) = ( P ( f x ) ( f y ) )",
    "( Conjunction (s xn) x y ) = ( ∃z ( ( Conjunction xn ( f z ) y ) ∧ ( P ( f x ) ( f z ) ) ) )" )

  val endSequent = Sequent(
    Seq(
      hof"!x (Disjunction(n,x))",
      hof"!y!z (Conjunction(n,y,z) -> P(f(y),g(z)))",
      hof"!x!y (P(x,y) -> P(x,f(y)))" ),
    Seq( hof"∃x∃y (P(x,g(y)))" ) )

  ctx += Context.ProofNameDeclaration( le"chi n", endSequent )

  val leftBranch = Sequent(
    Seq(
      hof"(Disjunction(n,alpha))",
      hof"!x!y (P(x,y) -> P(x,f(y)))" ),
    Seq(
      hof"∃x∃y (P(x,g(y)))",
      hof"∃y (P(alpha,f(y)))" ) )

  ctx += Context.ProofNameDeclaration( le"phi n alpha", leftBranch )

  val rightBranch = Sequent(
    Seq(
      hof"∀x∃y (P(x,f(y)))",
      hof"(P(f(beta1),f(beta2)))",
      hof"!y!z (Conjunction(n,y,z) -> P(f(y),g(z)))",
      hof"!z (Conjunction(n,a,z) -> P(f(a),g(z)))" ),
    Seq(
      hof"∃x∃y (P(x,g(y)))",
      hof"Conjunction(n,beta1,beta2)" ) )

  ctx += Context.ProofNameDeclaration( le"xhi n beta1 beta2", rightBranch )

  val esChiBc = Sequent(
    Seq(
      "Ant_0" -> hof"!x (Disjunction(0,x))",
      "Ant_1" -> hof"!y!z (Conjunction(0,y,z) -> P(f(y),g(z)))",
      "Ant_2" -> hof"!x!y (P(x,y) -> P(x,f(y)))" ),
    Seq( "Suc_0" -> hof"∃x∃y (P(x,g(y)))" ) )

  val chiBc = Lemma( esChiBc ) {
    cut( "Cut", hof"∀x∃y (P(x,f(y)))" )
    allR( "Cut", fov"alpha:i" )
    allL( "Ant_0", fot"alpha:i" )
    ref( "phi" )
    allL( "Cut", le"f a" )
    exL( "Cut_0", fov"beta:i" )
    allL( "Ant_1", foc"a" )
    allL( "Ant_1_0", fov"beta:i" )
    impL( "Ant_1_0_0" )
    focus( 1 )
    exR( "Suc_0", le"f a" )
    exR( "Suc_0_0", le"beta:i" )
    trivial
    ref( "xhi" )
  }

  ctx += Context.ProofDefinitionDeclaration( le"chi 0", chiBc )

  val esChiSc = Sequent(
    Seq(
      "Ant_0" -> hof"!x (Disjunction(s(n),x))",
      "Ant_1" -> hof"!y!z (Conjunction(s(n),y,z) -> P(f(y),g(z)))",
      "Ant_2" -> hof"!x!y (P(x,y) -> P(x,f(y)))" ),
    Seq( "Suc_0" -> hof"∃x∃y (P(x,g(y)))" ) )

  val chiSc = Lemma( esChiSc ) {
    cut( "Cut", hof"∀x∃y (P(x,f(y)))" )
    allR( "Cut", fov"alpha:i" )
    allL( "Ant_0", fot"alpha:i" )
    ref( "phi" )
    allL( "Cut", le"f a" )
    exL( "Cut_0", fov"beta:i" )
    allL( "Ant_1", foc"a" )
    allL( "Ant_1_0", fot"beta:i" )
    impL( "Ant_1_0_0" )
    focus( 1 )
    exR( "Suc_0", le"f a" )
    exR( "Suc_0_0", fot"beta:i" )
    trivial
    ref( "xhi" )
  }

  ctx += Context.ProofDefinitionDeclaration( le"chi (s n)", chiSc )

  val esPhiBc = Sequent(
    Seq(
      "Ant_alpha" -> hof"(Disjunction(0,alpha))",
      "Ant_2" -> hof"!x!y (P(x,y) -> P(x,f(y)))" ),
    Seq(
      "Suc_0" -> hof"∃x∃y (P(x,g(y)))",
      "CutF" -> hof"∃y (P(alpha,f(y)))" ) )

  val phiBc = Lemma( esPhiBc ) {
    exR( "CutF", le"fn 0 alpha:i" )
    exR( "CutF", le"fn ( s 0 ) alpha:i" )
    allL( "Ant_2", fot"alpha:i" )
    allL( "Ant_2_0", le"fn 0 alpha:i" )
    allL( "Ant_2_0", le"fn 1 alpha:i" )
    unfold( "Disjunction" ) atMost 1 in "Ant_alpha"
    escargot
  }

  ctx += Context.ProofDefinitionDeclaration( le"phi 0 alpha", phiBc )

  val esPhiSc = Sequent(
    Seq(
      "Ant_alpha" -> hof"(Disjunction(s(n),alpha))",
      "Ant_2" -> hof"!x!y (P(x,y) -> P(x,f(y)))" ),
    Seq(
      "Suc_0" -> hof"∃x∃y (P(x,g(y)))",
      "CutF" -> hof"∃y (P(alpha,f(y)))" ) )

  val phiSc = Lemma( esPhiSc ) {
    unfold( "Disjunction" ) atMost 1 in "Ant_alpha"
    orL( "Ant_alpha" )
    ref( "phi" )
    exR( "CutF", le"fn ( s n ) alpha:i" )
    allL( "Ant_2", fot"alpha:i" )
    allL( "Ant_2_0", le"fn ( s n ) alpha:i" )
    impL( "Ant_2_0_0" )
    trivial
    trivial
  }

  ctx += Context.ProofDefinitionDeclaration( le"phi (s n) alpha", phiSc )

  val esXhiBc = Sequent(
    Seq(
      "CutF" -> hof"∀x∃y (P(x,f(y)))",
      "CutF1" -> hof"(P(f(beta1:i),f(beta2:i)))",
      "Ant_1" -> hof"!y!z (Conjunction(0,y,z) -> P(f(y),g(z)))",
      "Ant_1_0" -> hof"!z (Conjunction(0,a,z) -> P(f(a),g(z)))" ),
    Seq(
      "Suc_0" -> hof"∃x∃y (P(x,g(y)))",
      "Suc_1" -> hof"Conjunction(0,beta1:i,beta2:i)" ) )

  val xhiBc = Lemma( esXhiBc ) {
    unfold( "Conjunction" ) atMost 1 in "Suc_1"
    trivial
  }

  ctx += Context.ProofDefinitionDeclaration( le"xhi 0 beta1 beta2", xhiBc )

  val esXhiSc = Sequent(
    Seq(
      "CutF" -> hof"∀x∃y (P(x,f(y)))",
      "CutF1" -> hof"(P(f(beta1:i),f(beta2:i)))",
      "Ant_1" -> hof"!y!z (Conjunction(s(n),y,z) -> P(f(y),g(z)))",
      "Ant_1_0" -> hof"!z (Conjunction(0,a,z) -> P(f(a),g(z)))" ),
    Seq(
      "Suc_0" -> hof"∃x∃y (P(x,g(y)))",
      "Suc_1" -> hof"Conjunction(s(n),beta1:i,beta2:i)" ) )

  val xhiSc = Lemma( esXhiSc ) {
    allL( "CutF", le"f beta2:i" )
    exL( "CutF_0", fov"beta3:i" )
    unfold( "Conjunction" ) atMost 1 in "Suc_1"
    exR( "Suc_1", fot"beta1:i" )
    andR( "Suc_1_0" )
    allL( "Ant_1_0", fot"beta3:i" )
    impL( "Ant_1_0_0" )
    focus( 1 )
    exR( "Suc_0", le"f a" )
    exR( "Suc_0_0", fot"beta3:i" )
    trivial
    ref( "xhi" )
    trivial
  }

  ctx += Context.ProofDefinitionDeclaration( le"xhi (s n) beta1 beta2", xhiSc )

}