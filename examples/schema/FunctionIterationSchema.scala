package gapt.examples

import gapt.proofs.{ Context, Sequent }
import gapt.proofs.Context._
import gapt.proofs.gaptic._
import gapt.expr._

object FunctionIterationSchema extends TacticsProof {
  ctx += Context.InductiveType( "nat", hoc"0 : nat", hoc"s : nat>nat" )
  ctx += Context.Sort( "i" )
  ctx += hoc"f:i>i"
  ctx += hoc"a:i"
  ctx += hoc"P: i>o"
  ctx += PrimRecFun( hoc"if:nat>i>i", "if 0 x = x", "if (s y) x = (f (if y x))" )
  ctx += hoc"phi: nat>nat"

  val esPhi = Sequent(
    Seq( hof"!x (-P(x) | P(f(x)))", hof"P(a)" ),
    Seq( hof"P(if(n,a))" ) )
  ctx += Context.ProofNameDeclaration( le"phi n", esPhi )

  val esPhiSc = Sequent(
    Seq(
      "Ant_1" -> hof"!x (-P(x) | P(f(x)))",
      "Ant_0" -> hof"P(a)" ),
    Seq( "Suc_0" -> hof"P(if(s(n),a))" ) )
  val phiSc = Lemma( esPhiSc ) {
    cut( "cut", hof"!x (-P(x) | P(f(x)))" ) left by {
      allR( "cut", fov"A" )
      allL( "Ant_1", fov"A" )
      orL
      orR
      negL
      negR
      trivial
      orR
      trivial
    }
    allL( "cut", le"(if n a)" )
    orL
    by {
      forget( "Suc_0" )
      forget( "cut" )
      negL
      ref( "phi" )
    }
    by {
      unfold( "if" ) atMost 1 in "Suc_0"
      trivial
    }
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi (s n)", phiSc )
  val esPhiBc = Sequent(
    Seq(
      "Ant_1" -> hof"!x (-P(x) | P(f(x)))",
      "Ant_0" -> hof"P(a)" ),
    Seq( "Suc_0" -> hof"P(if(0,a))" ) )
  val phiBc = Lemma( esPhiBc ) {
    unfold( "if" ) atMost 1 in "Suc_0"
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi 0", phiBc )

}
