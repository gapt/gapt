package gapt.examples

import gapt.examples.FirstSchema4.ctx
import gapt.examples.FirstSchema5.ctx
import gapt.expr._
import gapt.proofs.Context.{ PrimRecFun, _ }
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

  ctx += hoc"P: i>i>o"

  ctx += PrimRecFun(
    hoc"Disjunction: nat>i>o",
    "( Disjunction 0 x ) = ( ( P x ( fn 0 x ) ) ∨ ( P x ( fn (s 0) x ) ) )",
    "( Disjunction (s xn) x ) = ( ( Disjunction xn x ) ∨ ( P x ( fn (s xn) x ) ) )" )
  ctx += PrimRecFun(
    hoc"Conjunction: nat>i>i>o",
    "( Conjunction 0 x y ) = ( P x ( f y ) )",
    "( Conjunction (s xn) x y ) = ( ∃z ( ( Conjunction xn x z ) ∧ ( P ( f z ) ( f y ) ) ) )" )

  val endSequent = Sequent(
    Seq(
      hof"!x (Disjunction(n,x))",
      hof"!y!z (Conjunction(n,y,z) -> P(y,g(z)))",
      hof"!x!y (P(x,y) -> P(x,f(y)))" ),
    Seq( hof"∃x∃y (P(x,g(y)))" ) )

  ctx += Context.ProofNameDeclaration( le"chi n", endSequent )

  val leftBranch = Sequent(
    Seq(
      hof"(Disjunction(n,alpha))",
      hof"!x (Disjunction(n,x))",
      hof"!y!z (Conjunction(n,y,z) -> P(y,g(z)))",
      hof"!x!y (P(x,y) -> P(x,f(y)))" ),
    Seq(
      hof"∃x∃y (P(x,g(y)))",
      hof"∃y (P(alpha,f(y)))" ) )

  ctx += Context.ProofNameDeclaration( le"phi n alpha", leftBranch )

  val esChiBc = Sequent(
    Seq(
      "Ant_0" -> hof"!x (Disjunction(0,x))",
      "Ant_1" -> hof"!y!z (Conjunction(0,y,z) -> P(y,g(z)))",
      "Ant_2" -> hof"!x!y (P(x,y) -> P(x,f(y)))" ),
    Seq( "Suc_0" -> hof"∃x∃y (P(x,g(y)))" ) )

  val chiBc = Lemma( esChiBc ) {
    cut( "Cut", hof"∀x∃y (P(x,f(y)))" )
    allR( "Cut", fov"alpha:i" )
    allL( "Ant_0", fot"alpha:i" )
    ref( "phi" )
    trivial
  }

  ctx += Context.ProofDefinitionDeclaration( le"chi 0", chiBc )

  val esChiSc = Sequent(
    Seq(
      "Ant_0" -> hof"!x (Disjunction(s(n),x))",
      "Ant_1" -> hof"!y!z (Conjunction(s(n),y,z) -> P(y,g(z)))",
      "Ant_2" -> hof"!x!y (P(x,y) -> P(x,f(y)))" ),
    Seq( "Suc_0" -> hof"∃x∃y (P(x,g(y)))" ) )

  val chiSc = Lemma( esChiSc ) {
    cut( "Cut", hof"∀x∃y (P(x,f(y)))" )
    ref( "phi" )
    trivial
  }

  ctx += Context.ProofDefinitionDeclaration( le"chi (s n)", chiSc )

  val esPhiBc = Sequent(
    Seq(
      "Ant_alpha" -> hof"(Disjunction(0,alpha))",
      "Ant_0" -> hof"!x (Disjunction(0,x))",
      "Ant_1" -> hof"!y!z (Conjunction(0,y,z) -> P(y,g(z)))",
      "Ant_2" -> hof"!x!y (P(x,y) -> P(x,f(y)))" ),
    Seq(
      "Suc_0" -> hof"∃x∃y (P(x,g(y)))",
      "CutF" -> hof"∃y (P(alpha,f(y)))" ) )

  val phiBc = Lemma( esPhiBc ) {
    exR( "CutF", fot"fn(0,alpha:i)" )
    exR( "CutF", fot"fn(s(0),alpha:i)" )
    allL( "Ant_0", fot"alpha:i" )
    allL( "Ant_2", fot"alpha:i" )
    allL( "Ant_2_0", fot"fn(0,alpha:i)" )
    allL( "Ant_2_0", fot"fn(1,alpha:i)" )
    escargot
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi 0", phiBc )

  val esPhiSc = Sequent(
    Seq(
      "Ant_alpha" -> hof"(Disjunction(s(n),alpha))",
      "Ant_0" -> hof"!x (Disjunction(s(n),x))",
      "Ant_1" -> hof"!y!z (Conjunction(s(n),y,z) -> P(y,g(z)))",
      "Ant_2" -> hof"!x!y (P(x,y) -> P(x,f(y)))" ),
    Seq(
      "Suc_0" -> hof"∃x∃y (P(x,g(y)))",
      "CutF" -> hof"∃y (P(alpha,f(y)))" ) )

  val phiSc = Lemma( esPhiSc ) {
    unfold( "Disjunction" ) atMost 1 in "Ant_alpha"
    orL( "Ant_alpha" )
    ref( "phi" )
    exR( "CutF", fot"fn(s(n),alpha:i)" )
    allL( "Ant_2", fot"alpha:i" )
    allL( "Ant_2_0", fot"fn(s(n),alpha:i)" )
    impL( "Ant_2_0_0" )
    trivial
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi (s n)", phiSc )

}