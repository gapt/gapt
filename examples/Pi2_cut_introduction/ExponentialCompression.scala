package gapt.examples

import gapt.expr._
import gapt.proofs.gaptic._
import gapt.proofs.Sequent
import gapt.proofs.context.update.InductiveType
import gapt.proofs.context.update.ProofDefinitionDeclaration
import gapt.proofs.context.update.ProofNameDeclaration
import gapt.proofs.context.update.Sort
import gapt.proofs.context.update.PrimitiveRecursiveFunction

object ExponentialCompression extends TacticsProof {

  ctx += InductiveType( "nat", hoc"0 : nat", hoc"s : nat>nat" )
  ctx += Sort( "i" )

  ctx += hoc"a:i"
  ctx += hoc"f:i>i"
  ctx += hoc"g:i>i"
  ctx += hoc"fn:nat>i>i"

  ctx += hoc"omega: nat>nat"
  ctx += hoc"preOmega: nat>nat"
  ctx += hoc"chi: nat>nat"
  ctx += hoc"phi: nat>i>nat"
  ctx += hoc"xhi: nat>i>i>nat"
  ctx += hoc"preXhi: nat>i>i>nat>nat"
  ctx += hoc"tau: nat>nat"

  ctx += hoc"P: i>i>o"

  ctx += PrimitiveRecursiveFunction(
    hoc"Disjunction: nat>i>o",
    "( Disjunction 0 x ) = ( ( P x ( fn 0 x ) ) )",
    "( Disjunction (s xn) x ) = ( ( Disjunction xn x ) ∨ ( P x ( fn (s xn) x ) ) )" )
  ctx += PrimitiveRecursiveFunction(
    hoc"Conjunction: nat>i>i>o",
    "( Conjunction 0 y z ) = ( ( P ( f y ) ( f z ) ) )",
    "( Conjunction (s xn) x z ) = ( ∃y ( ( P ( f x ) ( f y ) ) ∧ ( Conjunction xn y z ) ) )" )

  //
  // endsequents of links:
  //

  val certainlyTheEndSequentForRealTrustMeDude = Sequent(
    Seq(),
    Seq( hof"(∃x1∃x2∃x3∃x4∃x5∃x6∃x7( -( (Conjunction(n,x1,x2) -> P(f(x1),g(x2)))) ∨ -( (Disjunction(n,x3))) ∨ -( (P(x4,x5) -> P(x4,f(x5)))) ∨ ( (P(x6,g(x7)))) ))" ) )

  ctx += ProofNameDeclaration( le"omega n", certainlyTheEndSequentForRealTrustMeDude )

  val endSequent = Sequent(
    Seq(),
    Seq( hof"( -(!x!z (Conjunction(n,x,z) -> P(f(x),g(z)))) ∨ -(!x (Disjunction(n,x))) ∨ -(!x!y (P(x,y) -> P(x,f(y)))) ∨ (∃x∃y (P(x,g(y)))) )" ) )

  ctx += ProofNameDeclaration( le"preOmega n", endSequent )

  val conjunction = Sequent(
    Seq(
      hof"!x (Disjunction(n,x))",
      hof"!x!y (P(x,y) -> P(x,f(y)))" ),
    Seq( hof"∃x∃z (Conjunction(n,x,z))" ) )

  ctx += ProofNameDeclaration( le"tau n", conjunction )

  val intermediateEndSequent = Sequent(
    Seq(
      hof"!x (Disjunction(n,x))",
      hof"!x!z (Conjunction(n,x,z) -> P(f(x),g(z)))",
      hof"!x!y (P(x,y) -> P(x,f(y)))" ),
    Seq( hof"∃x∃y (P(x,g(y)))" ) )

  ctx += ProofNameDeclaration( le"chi n", intermediateEndSequent )

  val leftBranch = Sequent(
    Seq(
      hof"(Disjunction(n,alpha))",
      hof"!x!y (P(x,y) -> P(x,f(y)))" ),
    Seq(
      hof"∃y (P(alpha,f(y)))" ) )

  ctx += ProofNameDeclaration( le"phi n alpha", leftBranch )

  val preRightBranch = Sequent(
    Seq(
      hof"( ( P ( f alpha ) ( f beta ) ) ∧ ∃z ( Conjunction na beta z ) )" ),
    Seq(
      hof"(∃z∃y ( ( P ( f alpha ) ( f y ) ) ∧ ( Conjunction na y z ) ) )" ) )

  ctx += ProofNameDeclaration( le"preXhi n alpha beta na", preRightBranch )

  val rightBranch = Sequent(
    Seq(
      hof"∀x∃y (P(x,f(y)))",
      hof"(P(f(beta1),f(beta2)))" ),
    Seq(
      hof"∃z (Conjunction(n,beta1,z))" ) )

  ctx += ProofNameDeclaration( le"xhi n beta1 beta2", rightBranch )

  //
  // proof pairs:
  //

  val esOmegaBc = Sequent(
    Seq(),
    Seq( "Suc_0" -> hof"(∃x1∃x2∃x3∃x4∃x5∃x6∃x7( -( (Conjunction(0,x1,x2) -> P(f(x1),g(x2)))) ∨ -( (Disjunction(0,x3))) ∨ -( (P(x4,x5) -> P(x4,f(x5)))) ∨ ( (P(x6,g(x7)))) ))" ) )

  val omegaBc = Lemma( esOmegaBc ) {
    cut( "Cut", hof"( -(!x!z (Conjunction(0,x,z) -> P(f(x),g(z)))) ∨ -(!x (Disjunction(0,x))) ∨ -(!x!y (P(x,y) -> P(x,f(y)))) ∨ (∃x∃y (P(x,g(y)))) )" )
    ref( "preOmega" )
    orL( "Cut" )
    orL( "Cut" )
    orL( "Cut" )
    negL( "Cut" )
    allR( "Cut", fov"alpha:i" )
    allR( "Cut", fov"beta:i" )
    exR( "Suc_0", le"alpha:i" )
    exR( "Suc_0_0", le"beta:i" )
    exR( "Suc_0_0_0", le"beta:i" )
    exR( "Suc_0_0_0_0", le"beta:i" )
    exR( "Suc_0_0_0_0_0", le"beta:i" )
    exR( "Suc_0_0_0_0_0_0", le"beta:i" )
    exR( "Suc_0_0_0_0_0_0_0", le"beta:i" )
    orR( "Suc_0_0_0_0_0_0_0_0" )
    orR( "Suc_0_0_0_0_0_0_0_0_0" )
    orR( "Suc_0_0_0_0_0_0_0_0_0_0" )
    negR( "Suc_0_0_0_0_0_0_0_0_0_0_0" )
    impR( "Cut" )
    impL( "Suc_0_0_0_0_0_0_0_0_0_0_0" )
    trivial
    trivial
    negL( "Cut" )
    allR( "Cut", fov"alpha:i" )
    exR( "Suc_0", le"alpha:i" )
    exR( "Suc_0_0", le"alpha:i" )
    exR( "Suc_0_0_0", le"alpha:i" )
    exR( "Suc_0_0_0_0", le"alpha:i" )
    exR( "Suc_0_0_0_0_0", le"alpha:i" )
    exR( "Suc_0_0_0_0_0_0", le"alpha:i" )
    exR( "Suc_0_0_0_0_0_0_0", le"alpha:i" )
    orR( "Suc_0_0_0_0_0_0_0_0" )
    orR( "Suc_0_0_0_0_0_0_0_0_0" )
    orR( "Suc_0_0_0_0_0_0_0_0_0_0" )
    negR( "Suc_0_0_0_0_0_0_0_0_0_0_1" )
    trivial
    negL( "Cut" )
    allR( "Cut", fov"alpha:i" )
    allR( "Cut", fov"beta:i" )
    exR( "Suc_0", le"alpha:i" )
    exR( "Suc_0_0", le"alpha:i" )
    exR( "Suc_0_0_0", le"alpha:i" )
    exR( "Suc_0_0_0_0", le"alpha:i" )
    exR( "Suc_0_0_0_0_0", le"beta:i" )
    exR( "Suc_0_0_0_0_0_0", le"beta:i" )
    exR( "Suc_0_0_0_0_0_0_0", le"beta:i" )
    orR( "Suc_0_0_0_0_0_0_0_0" )
    orR( "Suc_0_0_0_0_0_0_0_0_0" )
    negR( "Suc_0_0_0_0_0_0_0_0_0_1" )
    impR( "Cut" )
    impL( "Suc_0_0_0_0_0_0_0_0_0_1" )
    trivial
    trivial
    exL( "Cut", fov"alpha:i" )
    exL( "Cut", fov"beta:i" )
    exR( "Suc_0", le"alpha:i" )
    exR( "Suc_0_0", le"alpha:i" )
    exR( "Suc_0_0_0", le"alpha:i" )
    exR( "Suc_0_0_0_0", le"alpha:i" )
    exR( "Suc_0_0_0_0_0", le"alpha:i" )
    exR( "Suc_0_0_0_0_0_0", le"alpha:i" )
    exR( "Suc_0_0_0_0_0_0_0", le"beta:i" )
    orR( "Suc_0_0_0_0_0_0_0_0" )
    trivial
  }

  ctx += ProofDefinitionDeclaration( le"omega 0", omegaBc )

  val esOmegaSc = Sequent(
    Seq(),
    Seq( "Suc_0" -> hof"(∃x1∃x2∃x3∃x4∃x5∃x6∃x7( -( (Conjunction(s(n),x1,x2) -> P(f(x1),g(x2)))) ∨ -( (Disjunction(s(n),x3))) ∨ -( (P(x4,x5) -> P(x4,f(x5)))) ∨ ( (P(x6,g(x7)))) ))" ) )

  val omegaSc = Lemma( esOmegaSc ) {
    cut( "Cut", hof"( -(!x!z (Conjunction(s(n),x,z) -> P(f(x),g(z)))) ∨ -(!x (Disjunction(s(n),x))) ∨ -(!x!y (P(x,y) -> P(x,f(y)))) ∨ (∃x∃y (P(x,g(y)))) )" )
    ref( "preOmega" )
    orL( "Cut" )
    orL( "Cut" )
    orL( "Cut" )
    negL( "Cut" )
    allR( "Cut", fov"alpha:i" )
    allR( "Cut", fov"beta:i" )
    exR( "Suc_0", le"alpha:i" )
    exR( "Suc_0_0", le"beta:i" )
    exR( "Suc_0_0_0", le"beta:i" )
    exR( "Suc_0_0_0_0", le"beta:i" )
    exR( "Suc_0_0_0_0_0", le"beta:i" )
    exR( "Suc_0_0_0_0_0_0", le"beta:i" )
    exR( "Suc_0_0_0_0_0_0_0", le"beta:i" )
    orR( "Suc_0_0_0_0_0_0_0_0" )
    orR( "Suc_0_0_0_0_0_0_0_0_0" )
    orR( "Suc_0_0_0_0_0_0_0_0_0_0" )
    negR( "Suc_0_0_0_0_0_0_0_0_0_0_0" )
    impR( "Cut" )
    impL( "Suc_0_0_0_0_0_0_0_0_0_0_0" )
    trivial
    trivial
    negL( "Cut" )
    allR( "Cut", fov"alpha:i" )
    exR( "Suc_0", le"alpha:i" )
    exR( "Suc_0_0", le"alpha:i" )
    exR( "Suc_0_0_0", le"alpha:i" )
    exR( "Suc_0_0_0_0", le"alpha:i" )
    exR( "Suc_0_0_0_0_0", le"alpha:i" )
    exR( "Suc_0_0_0_0_0_0", le"alpha:i" )
    exR( "Suc_0_0_0_0_0_0_0", le"alpha:i" )
    orR( "Suc_0_0_0_0_0_0_0_0" )
    orR( "Suc_0_0_0_0_0_0_0_0_0" )
    orR( "Suc_0_0_0_0_0_0_0_0_0_0" )
    negR( "Suc_0_0_0_0_0_0_0_0_0_0_1" )
    trivial
    negL( "Cut" )
    allR( "Cut", fov"alpha:i" )
    allR( "Cut", fov"beta:i" )
    exR( "Suc_0", le"alpha:i" )
    exR( "Suc_0_0", le"alpha:i" )
    exR( "Suc_0_0_0", le"alpha:i" )
    exR( "Suc_0_0_0_0", le"alpha:i" )
    exR( "Suc_0_0_0_0_0", le"beta:i" )
    exR( "Suc_0_0_0_0_0_0", le"beta:i" )
    exR( "Suc_0_0_0_0_0_0_0", le"beta:i" )
    orR( "Suc_0_0_0_0_0_0_0_0" )
    orR( "Suc_0_0_0_0_0_0_0_0_0" )
    negR( "Suc_0_0_0_0_0_0_0_0_0_1" )
    impR( "Cut" )
    impL( "Suc_0_0_0_0_0_0_0_0_0_1" )
    trivial
    trivial
    exL( "Cut", fov"alpha:i" )
    exL( "Cut", fov"beta:i" )
    exR( "Suc_0", le"alpha:i" )
    exR( "Suc_0_0", le"alpha:i" )
    exR( "Suc_0_0_0", le"alpha:i" )
    exR( "Suc_0_0_0_0", le"alpha:i" )
    exR( "Suc_0_0_0_0_0", le"alpha:i" )
    exR( "Suc_0_0_0_0_0_0", le"alpha:i" )
    exR( "Suc_0_0_0_0_0_0_0", le"beta:i" )
    orR( "Suc_0_0_0_0_0_0_0_0" )
    trivial
  }

  ctx += ProofDefinitionDeclaration( le"omega (s n)", omegaSc )

  val esPreOmegaBc = Sequent(
    Seq(),
    Seq( "Suc_0" -> hof"( -(!x!z (Conjunction(0,x,z) -> P(f(x),g(z)))) ∨ -(!x (Disjunction(0,x))) ∨ -(!x!y (P(x,y) -> P(x,f(y)))) ∨ (∃x∃y (P(x,g(y)))) )" ) )

  val preOmegaBc = Lemma( esPreOmegaBc ) {
    orR( "Suc_0" )
    orR( "Suc_0_0" )
    orR( "Suc_0_0_0" )
    negR( "Suc_0_0_1" )
    negR( "Suc_0_0_0_0" )
    negR( "Suc_0_0_0_1" )
    ref( "chi" )
  }

  ctx += ProofDefinitionDeclaration( le"preOmega 0", preOmegaBc )

  val esPreOmegaSc = Sequent(
    Seq(),
    Seq( "Suc_0" -> hof"( -(!x!z (Conjunction(s(n),x,z) -> P(f(x),g(z)))) ∨ -(!x (Disjunction(s(n),x))) ∨ -(!x!y (P(x,y) -> P(x,f(y)))) ∨ (∃x∃y (P(x,g(y)))) )" ) )

  val preOmegaSc = Lemma( esPreOmegaSc ) {
    orR( "Suc_0" )
    orR( "Suc_0_0" )
    orR( "Suc_0_0_0" )
    negR( "Suc_0_0_1" )
    negR( "Suc_0_0_0_0" )
    negR( "Suc_0_0_0_1" )
    ref( "chi" )
  }

  ctx += ProofDefinitionDeclaration( le"preOmega (s n)", preOmegaSc )

  val esTauBc = Sequent(
    Seq(
      "Ant_0" -> hof"!x (Disjunction(0,x))",
      "Ant_1" -> hof"!x!y (P(x,y) -> P(x,f(y)))" ),
    Seq( "Suc_0" -> hof"∃x∃z (Conjunction(0,x,z))" ) )

  val tauBc = Lemma( esTauBc ) {
    unfold( "Disjunction" ) atMost 1 in "Ant_0"
    unfold( "Conjunction" ) atMost 1 in "Suc_0"
    allL( "Ant_0", le"f a" )
    allL( "Ant_1", le"f a" )
    allL( "Ant_1_0", le"fn 0 (f a)" )
    exR( "Suc_0", fot"a" )
    exR( "Suc_0_0", le"fn 0 (f a)" )
    impL( "Ant_1_0_0" )
    trivial
    trivial
  }

  ctx += ProofDefinitionDeclaration( le"tau 0", tauBc )

  val esTauSc = Sequent(
    Seq(
      "Ant_0" -> hof"!x (Disjunction(s(n),x))",
      "Ant_1" -> hof"!x!y (P(x,y) -> P(x,f(y)))" ),
    Seq( "Suc_0" -> hof"∃x∃z (Conjunction(s(n),x,z))" ) )

  val tauSc = Lemma( esTauSc ) {
    cut( "Cut", hof"∀x∃y (P(x,f(y)))" )
    allR( "Cut", fov"alpha:i" )
    allL( "Ant_0", fot"alpha:i" )
    ref( "phi" )
    allL( "Cut", le"f a" )
    exL( "Cut_0", fov"beta" )
    exR( "Suc_0", fot"a" )
    ref( "xhi" )
  }

  ctx += ProofDefinitionDeclaration( le"tau (s n)", tauSc )

  val esChiBc = Sequent(
    Seq(
      "Ant_0" -> hof"!x (Disjunction(0,x))",
      "Ant_1" -> hof"!x!z (Conjunction(0,x,z) -> P(f(x),g(z)))",
      "Ant_2" -> hof"!x!y (P(x,y) -> P(x,f(y)))" ),
    Seq( "Suc_0" -> hof"∃x∃y (P(x,g(y)))" ) )

  val chiBc = Lemma( esChiBc ) {
    cut( "Cut", hof"∃x∃z (Conjunction(0,x,z))" )
    ref( "tau" )
    exL( "Cut", fov"alpha:i" )
    exL( "Cut", fov"beta:i" )
    allL( "Ant_1", fov"alpha:i" )
    allL( "Ant_1_0", fov"beta:i" )
    impL( "Ant_1_0_0" )
    focus( 1 )
    exR( "Suc_0", le"f alpha:i" )
    exR( "Suc_0_0", le"beta:i" )
    unfold( "Conjunction" ) atMost 1 in "Cut"
    trivial
    unfold( "Conjunction" ) atMost 1 in "Cut"
    unfold( "Conjunction" ) atMost 1 in "Ant_1_0_0"
    trivial
  }

  ctx += ProofDefinitionDeclaration( le"chi 0", chiBc )

  val esChiSc = Sequent(
    Seq(
      "Ant_0" -> hof"!x (Disjunction(s(n),x))",
      "Ant_1" -> hof"!x!z (Conjunction(s(n),x,z) -> P(f(x),g(z)))",
      "Ant_2" -> hof"!x!y (P(x,y) -> P(x,f(y)))" ),
    Seq( "Suc_0" -> hof"∃x∃y (P(x,g(y)))" ) )

  val chiSc = Lemma( esChiSc ) {
    cut( "Cut", hof"∃x∃z (Conjunction(s(n),x,z))" )
    ref( "tau" )
    exL( "Cut", fov"alpha:i" )
    exL( "Cut", fov"beta:i" )
    allL( "Ant_1", fov"alpha:i" )
    allL( "Ant_1_0", fov"beta:i" )
    impL( "Ant_1_0_0" )
    focus( 1 )
    exR( "Suc_0", le"f alpha:i" )
    exR( "Suc_0_0", le"beta:i" )
    unfold( "Conjunction" ) atMost 1 in "Cut"
    trivial
    unfold( "Conjunction" ) atMost 1 in "Cut"
    unfold( "Conjunction" ) atMost 1 in "Ant_1_0_0"
    trivial
  }

  ctx += ProofDefinitionDeclaration( le"chi (s n)", chiSc )

  val esPhiBc = Sequent(
    Seq(
      "Ant_alpha" -> hof"(Disjunction(0,alpha))",
      "Ant_2" -> hof"!x!y (P(x,y) -> P(x,f(y)))" ),
    Seq(
      "CutF" -> hof"∃y (P(alpha,f(y)))" ) )

  val phiBc = Lemma( esPhiBc ) {
    exR( "CutF", le"fn 0 alpha:i" )
    allL( "Ant_2", fot"alpha:i" )
    allL( "Ant_2_0", le"fn 0 alpha:i" )
    unfold( "Disjunction" ) atMost 1 in "Ant_alpha"
    impL( "Ant_2_0_0" )
    trivial
    trivial
  }

  ctx += ProofDefinitionDeclaration( le"phi 0 alpha", phiBc )

  val esPhiSc = Sequent(
    Seq(
      "Ant_alpha" -> hof"(Disjunction(s(n),alpha))",
      "Ant_2" -> hof"!x!y (P(x,y) -> P(x,f(y)))" ),
    Seq(
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

  ctx += ProofDefinitionDeclaration( le"phi (s n) alpha", phiSc )

  val esXhiBc = Sequent(
    Seq(
      "CutF" -> hof"∀x∃y (P(x,f(y)))",
      "CutF1" -> hof"(P(f(beta1:i),f(beta2:i)))" ),
    Seq(
      "Suc_1" -> hof"∃z (Conjunction(0,beta1:i,z))" ) )

  val xhiBc = Lemma( esXhiBc ) {
    unfold( "Conjunction" ) atMost 1 in "Suc_1"
    exR( "Suc_1", fot"beta2:i" )
    trivial
  }

  ctx += ProofDefinitionDeclaration( le"xhi 0 beta1 beta2", xhiBc )

  val esXhiSc = Sequent(
    Seq(
      "CutF" -> hof"∀x∃y (P(x,f(y)))",
      "CutF1" -> hof"(P(f(beta1:i),f(beta2:i)))" ),
    Seq(
      "Suc_1" -> hof"∃z (Conjunction(s(n),beta1:i,z))" ) )

  val xhiSc = Lemma( esXhiSc ) {
    cut( "Cut", hof"( ( P ( f beta1:i ) ( f beta2:i ) ) ∧ ∃z ( Conjunction n beta2 z ) )" )
    allL( "CutF", le"f beta2:i" )
    exL( "CutF_0", fov"beta3:i" )
    andR( "Cut" )
    trivial
    forget( "CutF1" )
    ref( "xhi" )
    unfold( "Conjunction" ) atMost 1 in "Suc_1"
    ref( "preXhi" )
  }

  ctx += ProofDefinitionDeclaration( le"xhi (s n) beta1 beta2", xhiSc )

  val esPreXhiBc = Sequent(
    Seq(
      "Ant_0" -> hof"( ( P ( f alpha ) ( f beta ) ) ∧ ∃z ( Conjunction na beta z ) )" ),
    Seq(
      "Suc_0" -> hof"(∃z∃y ( ( P ( f alpha ) ( f y ) ) ∧ ( Conjunction na y z ) ) )" ) )

  val preXhiBc = Lemma( esPreXhiBc ) {
    andL( "Ant_0" )
    exL( "Ant_0_1", fov"gamma" )
    exR( "Suc_0", le"gamma:i" )
    exR( "Suc_0_0", le"beta:i" )
    andR( "Suc_0_0_0" )
    trivial
    trivial
  }

  ctx += ProofDefinitionDeclaration( le"preXhi 0 alpha beta na", preXhiBc )

  val esPreXhiSc = Sequent(
    Seq(
      "Ant_0" -> hof"( ( P ( f alpha ) ( f beta ) ) ∧ ∃z ( Conjunction na beta z ) )" ),
    Seq(
      "Suc_0" -> hof"(∃z∃y ( ( P ( f alpha ) ( f y ) ) ∧ ( Conjunction na y z ) ) )" ) )

  val preXhiSc = Lemma( esPreXhiSc ) {
    andL( "Ant_0" )
    exL( "Ant_0_1", fov"gamma" )
    exR( "Suc_0", le"gamma:i" )
    exR( "Suc_0_0", le"beta:i" )
    andR( "Suc_0_0_0" )
    trivial
    trivial
  }

  ctx += ProofDefinitionDeclaration( le"preXhi (s n) alpha beta na", preXhiSc )

}