package at.logic.gapt.examples

import at.logic.gapt.proofs.{ Context, Sequent }
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.expr._

object SimpleMutualInductionSchema extends TacticsProof {
  ctx += Context.InductiveType( "nat", hoc"0 : nat", hoc"s : nat>nat" )
  ctx += hoc"R: nat>nat>nat>o"
  ctx += hoc"phi: nat>nat"
  ctx += hoc"chi: nat>nat"
  ctx += hoc"omega: nat>nat"
  ctx += hoc"epsilon: nat>nat>nat"
  ctx += hoc"delta: nat>nat>nat>nat"
  val esdelta = Sequent(
    Seq(
      hof"!x (R(0,x,0))",
      hof"!x !y (-R(y,x,y) | R(0,y,s(x)))",
      hof"!x !y (-R(x,x,s(x)) | R(s(x),y,0))",
      hof"!x !y !z (-R(x,x,s(x)) | -R(y,z,y) | R(s(x),y,s(z)))" ),
    Seq( hof"R(n,m,k)" ) )
  ctx += Context.ProofNameDeclaration( le"delta n m k", esdelta )
  val esEpsilon = Sequent(
    Seq(
      hof"!x (R(0,x,0))",
      hof"!x !y (-R(y,x,y) | R(0,y,s(x)))",
      hof"!x !y (-R(x,x,s(x)) | R(s(x),y,0))",
      hof"!x !y !z (-R(x,x,s(x)) | -R(y,z,y) | R(s(x),y,s(z)))" ),
    Seq( hof"R(n,m,n)" ) )
  ctx += Context.ProofNameDeclaration( le"epsilon n m", esEpsilon )
  val esOmega = Sequent(
    Seq(
      hof"!x (R(0,x,0))",
      hof"!x !y (-R(y,x,y) | R(0,y,s(x)))",
      hof"!x !y (-R(x,x,s(x)) | R(s(x),y,0))",
      hof"!x !y !z (-R(x,x,s(x)) | -R(y,z,y) | R(s(x),y,s(z)))" ),
    Seq( hof"R(n,0,n)" ) )
  ctx += Context.ProofNameDeclaration( le"omega n", esOmega )
  val esPhi = Sequent(
    Seq(
      hof"!x (R(0,x,0))",
      hof"!x !y (-R(y,x,y) | R(0,y,s(x)))",
      hof"!x !y (-R(x,x,s(x)) | R(s(x),y,0))",
      hof"!x !y !z (-R(x,x,s(x)) | -R(y,z,y) | R(s(x),y,s(z)))" ),
    Seq( hof"R(n,n,s(n))" ) )
  ctx += Context.ProofNameDeclaration( le"phi n", esPhi )
  val esChi = Sequent(
    Seq(
      hof"!x (R(0,x,0))",
      hof"!x !y (-R(y,x,y) | R(0,y,s(x)))",
      hof"!x !y (-R(x,x,s(x)) | R(s(x),y,0))",
      hof"!x !y !z (-R(x,x,s(x)) | -R(y,z,y) | R(s(x),y,s(z)))" ),
    Seq( hof"R(n,n,n)" ) )
  ctx += Context.ProofNameDeclaration( le"chi n", esChi )

  val esPhiSc = Sequent(
    Seq(
      "Ant_0" -> hof"!x (R(0,x,0))",
      "Ant_1" -> hof"!x !y (-R(y,x,y) | R(0,y,s(x)))",
      "Ant_2" -> hof"!x !y (-R(x,x,s(x)) | R(s(x),y,0))",
      "Ant_3" -> hof"!x !y !z (-R(x,x,s(x)) | -R(y,z,y) | R(s(x),y,s(z)))" ),
    Seq( "Suc_0" -> hof"R(s(n),s(n),s(s(n)))" ) )
  val phiSc = Lemma( esPhiSc ) {
    allL( "Ant_3", le"n:nat" )
    allL( "Ant_3_0", le"(s n:nat)" )
    allL( "Ant_3_0_0", le"(s n:nat)" )
    orL
    orL
    negL
    forget( "Suc_0" )
    ref( "phi" )
    negL
    forget( "Suc_0" )
    ref( "chi" )
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi (s n)", phiSc )
  val esPhiBc = Sequent(
    Seq(
      "Ant_0" -> hof"!x (R(0,x,0))",
      "Ant_1" -> hof"!x !y (-R(y,x,y) | R(0,y,s(x)))",
      "Ant_2" -> hof"!x !y (-R(x,x,s(x)) | R(s(x),y,0))",
      "Ant_3" -> hof"!x !y !z (-R(x,x,s(x)) | -R(y,z,y) | R(s(x),y,s(z)))" ),
    Seq( "Suc_0" -> hof"R(0,0,s(0))" ) )
  val phiBc = Lemma( esPhiBc ) { escargot }
  ctx += Context.ProofDefinitionDeclaration( le"phi 0", phiBc )

  val esChiSc = Sequent(
    Seq(
      "Ant_0" -> hof"!x (R(0,x,0))",
      "Ant_1" -> hof"!x !y (-R(y,x,y) | R(0,y,s(x)))",
      "Ant_2" -> hof"!x !y (-R(x,x,s(x)) | R(s(x),y,0))",
      "Ant_3" -> hof"!x !y !z (-R(x,x,s(x)) | -R(y,z,y) | R(s(x),y,s(z)))" ),
    Seq( "Suc_0" -> hof"R(s(n),s(n),s(n))" ) )
  val chiSc = Lemma( esChiSc ) {
    allL( "Ant_3", le"n:nat" )
    allL( "Ant_3_0", le"(s n:nat)" )
    allL( "Ant_3_0_0", le"n:nat" )
    orL
    orL
    negL
    forget( "Suc_0" )
    ref( "phi" )
    negL
    forget( "Suc_0" )
    allL( "Ant_3", le"n:nat" )
    allL( "Ant_3_1", le"n:nat" )
    allL( "Ant_3_1_0", le"n:nat" )
    orL
    orL
    negL
    forget( "Ant_3_0_0_0" )
    ref( "phi" )
    negL
    forget( "Ant_3_0_0_0" )
    ref( "chi" )
    trivial
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"chi (s n)", chiSc )

  val esChiBc = Sequent(
    Seq(
      "Ant_0" -> hof"!x (R(0,x,0))",
      "Ant_1" -> hof"!x !y (-R(y,x,y) | R(0,y,s(x)))",
      "Ant_2" -> hof"!x !y (-R(x,x,s(x)) | R(s(x),y,0))",
      "Ant_3" -> hof"!x !y !z (-R(x,x,s(x)) | -R(y,z,y) | R(s(x),y,s(z)))" ),
    Seq( "Suc_0" -> hof"R(0,0,0)" ) )
  val chiBc = Lemma( esChiBc ) {
    escargot
  }
  ctx += Context.ProofDefinitionDeclaration( le"chi 0", chiBc )

  val esOmegaSc = Sequent(
    Seq(
      "Ant_0" -> hof"!x (R(0,x,0))",
      "Ant_1" -> hof"!x !y (-R(y,x,y) | R(0,y,s(x)))",
      "Ant_2" -> hof"!x !y (-R(x,x,s(x)) | R(s(x),y,0))",
      "Ant_3" -> hof"!x !y !z (-R(x,x,s(x)) | -R(y,z,y) | R(s(x),y,s(z)))" ),
    Seq( "Suc_0" -> hof"R(s(n),0,s(n))" ) )
  val omegaSc = Lemma( esOmegaSc ) {
    allL( "Ant_3", le"n:nat" )
    allL( "Ant_3_0", le"0" )
    allL( "Ant_3_0_0", le"n:nat" )
    orL
    orL
    negL
    forget( "Suc_0" )
    ref( "phi" )
    negL
    forget( "Suc_0" )
    allL( "Ant_0", le"n:nat" )
    trivial
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"omega (s n)", omegaSc )

  val esOmegaBc = Sequent(
    Seq(
      "Ant_0" -> hof"!x (R(0,x,0))",
      "Ant_1" -> hof"!x !y (-R(y,x,y) | R(0,y,s(x)))",
      "Ant_2" -> hof"!x !y (-R(x,x,s(x)) | R(s(x),y,0))",
      "Ant_3" -> hof"!x !y !z (-R(x,x,s(x)) | -R(y,z,y) | R(s(x),y,s(z)))" ),
    Seq( "Suc_0" -> hof"R(0,0,0)" ) )
  val omegaBc = Lemma( esOmegaBc ) {
    ref( "chi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"omega 0", omegaBc )

  val esEpsilonSc = Sequent(
    Seq(
      "Ant_0" -> hof"!x (R(0,x,0))",
      "Ant_1" -> hof"!x !y (-R(y,x,y) | R(0,y,s(x)))",
      "Ant_2" -> hof"!x !y (-R(x,x,s(x)) | R(s(x),y,0))",
      "Ant_3" -> hof"!x !y !z (-R(x,x,s(x)) | -R(y,z,y) | R(s(x),y,s(z)))" ),
    Seq( "Suc_0" -> hof"R(s(n),s(m),s(n))" ) )
  val epsilonSc = Lemma( esEpsilonSc ) {
    allL( "Ant_3", le"n:nat" )
    allL( "Ant_3_0", le"(s m)" )
    allL( "Ant_3_0_0", le"n:nat" )
    orL
    orL
    negL
    forget( "Suc_0" )
    ref( "phi" )
    negL
    forget( "Suc_0" )
    allL( "Ant_3", le"m:nat" )
    allL( "Ant_3_1", le"n:nat" )
    allL( "Ant_3_1_0", le"m:nat" )
    orL
    orL
    negL
    forget( "Ant_3_0_0_0" )
    ref( "phi" )
    negL
    forget( "Ant_3_0_0_0" )
    ref( "epsilon" )
    trivial
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"epsilon (s n) (s m)", epsilonSc )

  val esEpsilonBc = Sequent(
    Seq(
      "Ant_0" -> hof"!x (R(0,x,0))",
      "Ant_1" -> hof"!x !y (-R(y,x,y) | R(0,y,s(x)))",
      "Ant_2" -> hof"!x !y (-R(x,x,s(x)) | R(s(x),y,0))",
      "Ant_3" -> hof"!x !y !z (-R(x,x,s(x)) | -R(y,z,y) | R(s(x),y,s(z)))" ),
    Seq( "Suc_0" -> hof"R(s(n),0,s(n))" ) )
  val epsilonBc = Lemma( esEpsilonBc ) {
    ref( "omega" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"epsilon (s n) 0", epsilonBc )
  val esEpsilonBc2 = Sequent(
    Seq(
      "Ant_0" -> hof"!x (R(0,x,0))",
      "Ant_1" -> hof"!x !y (-R(y,x,y) | R(0,y,s(x)))",
      "Ant_2" -> hof"!x !y (-R(x,x,s(x)) | R(s(x),y,0))",
      "Ant_3" -> hof"!x !y !z (-R(x,x,s(x)) | -R(y,z,y) | R(s(x),y,s(z)))" ),
    Seq( "Suc_0" -> hof"R(0,(s m),0)" ) )
  val epsilonBc2 = Lemma( esEpsilonBc2 ) {
    allL( "Ant_0", le"(s m:nat)" )
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"epsilon 0 (s m)", epsilonBc2 )
  val esEpsilonBc3 = Sequent(
    Seq(
      "Ant_0" -> hof"!x (R(0,x,0))",
      "Ant_1" -> hof"!x !y (-R(y,x,y) | R(0,y,s(x)))",
      "Ant_2" -> hof"!x !y (-R(x,x,s(x)) | R(s(x),y,0))",
      "Ant_3" -> hof"!x !y !z (-R(x,x,s(x)) | -R(y,z,y) | R(s(x),y,s(z)))" ),
    Seq( "Suc_0" -> hof"R(0,0,0)" ) )
  val epsilonBc3 = Lemma( esEpsilonBc3 ) {
    allL( "Ant_0", le"0" )
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"epsilon 0 0", epsilonBc3 )

  val esDeltaSc = Sequent(
    Seq(
      "Ant_0" -> hof"!x (R(0,x,0))",
      "Ant_1" -> hof"!x !y (-R(y,x,y) | R(0,y,s(x)))",
      "Ant_2" -> hof"!x !y (-R(x,x,s(x)) | R(s(x),y,0))",
      "Ant_3" -> hof"!x !y !z (-R(x,x,s(x)) | -R(y,z,y) | R(s(x),y,s(z)))" ),
    Seq( "Suc_0" -> hof"R(s(n),s(m),s(k))" ) )
  val deltaSc = Lemma( esDeltaSc ) {
    allL( "Ant_3", le"n:nat" )
    allL( "Ant_3_0", le"(s m:nat)" )
    allL( "Ant_3_0_0", le"k:nat" )
    orL
    orL
    negL
    forget( "Suc_0" )
    ref( "phi" )
    negL
    forget( "Suc_0" )
    ref( "epsilon" )
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"delta (s n) (s m) (s k)", deltaSc )
  val esdeltaBc = Sequent(
    Seq(
      "Ant_0" -> hof"!x (R(0,x,0))",
      "Ant_1" -> hof"!x !y (-R(y,x,y) | R(0,y,s(x)))",
      "Ant_2" -> hof"!x !y (-R(x,x,s(x)) | R(s(x),y,0))",
      "Ant_3" -> hof"!x !y !z (-R(x,x,s(x)) | -R(y,z,y) | R(s(x),y,s(z)))" ),
    Seq( "Suc_0" -> hof"R(s(n),0,0)" ) )
  val deltaBc = Lemma( esdeltaBc ) {
    allL( "Ant_2", le"n:nat" )
    allL( "Ant_2_0", le"0" )
    orL
    negL
    forget( "Suc_0" )
    ref( "phi" )
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"delta (s n) 0 0", deltaBc )
  val esdeltaBc2 = Sequent(
    Seq(
      "Ant_0" -> hof"!x (R(0,x,0))",
      "Ant_1" -> hof"!x !y (-R(y,x,y) | R(0,y,s(x)))",
      "Ant_2" -> hof"!x !y (-R(x,x,s(x)) | R(s(x),y,0))",
      "Ant_3" -> hof"!x !y !z (-R(x,x,s(x)) | -R(y,z,y) | R(s(x),y,s(z)))" ),
    Seq( "Suc_0" -> hof"R(0,s(m),0)" ) )
  val deltaBc2 = Lemma( esdeltaBc2 ) {
    ref( "epsilon" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"delta 0 (s m) 0", deltaBc2 )
  val esdeltaBc3 = Sequent(
    Seq(
      "Ant_0" -> hof"!x (R(0,x,0))",
      "Ant_1" -> hof"!x !y (-R(y,x,y) | R(0,y,s(x)))",
      "Ant_2" -> hof"!x !y (-R(x,x,s(x)) | R(s(x),y,0))",
      "Ant_3" -> hof"!x !y !z (-R(x,x,s(x)) | -R(y,z,y) | R(s(x),y,s(z)))" ),
    Seq( "Suc_0" -> hof"R(0,0,s(k))" ) )
  val deltaBc3 = Lemma( esdeltaBc3 ) {
    allL( "Ant_1", le"k:nat" )
    allL( "Ant_1_0", le"0" )
    orL
    negL
    forget( "Suc_0" )
    ref( "epsilon" )
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"delta 0 0 (s k)", deltaBc3 )
  val esdeltaBc4 = Sequent(
    Seq(
      "Ant_0" -> hof"!x (R(0,x,0))",
      "Ant_1" -> hof"!x !y (-R(y,x,y) | R(0,y,s(x)))",
      "Ant_2" -> hof"!x !y (-R(x,x,s(x)) | R(s(x),y,0))",
      "Ant_3" -> hof"!x !y !z (-R(x,x,s(x)) | -R(y,z,y) | R(s(x),y,s(z)))" ),
    Seq( "Suc_0" -> hof"R(s(n),0,s(k))" ) )
  val deltaBc4 = Lemma( esdeltaBc4 ) {
    allL( "Ant_3", le"n:nat" )
    allL( "Ant_3_0", le"0" )
    allL( "Ant_3_0_0", le"k:nat" )
    orL
    orL
    negL
    forget( "Suc_0" )
    ref( "phi" )
    negL
    forget( "Suc_0" )
    ref( "epsilon" )
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"delta (s n) 0 (s k)", deltaBc4 )

  val esdeltaBc5 = Sequent(
    Seq(
      "Ant_0" -> hof"!x (R(0,x,0))",
      "Ant_1" -> hof"!x !y (-R(y,x,y) | R(0,y,s(x)))",
      "Ant_2" -> hof"!x !y (-R(x,x,s(x)) | R(s(x),y,0))",
      "Ant_3" -> hof"!x !y !z (-R(x,x,s(x)) | -R(y,z,y) | R(s(x),y,s(z)))" ),
    Seq( "Suc_0" -> hof"R(0,s(m),s(k))" ) )
  val deltaBc5 = Lemma( esdeltaBc5 ) {
    allL( "Ant_1", le"k:nat" )
    allL( "Ant_1_0", le"(s m:nat)" )
    orL
    negL
    forget( "Suc_0" )
    ref( "epsilon" )
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"delta 0 (s m) (s k)", deltaBc5 )

  val esdeltaBc6 = Sequent(
    Seq(
      "Ant_0" -> hof"!x (R(0,x,0))",
      "Ant_1" -> hof"!x !y (-R(y,x,y) | R(0,y,s(x)))",
      "Ant_2" -> hof"!x !y (-R(x,x,s(x)) | R(s(x),y,0))",
      "Ant_3" -> hof"!x !y !z (-R(x,x,s(x)) | -R(y,z,y) | R(s(x),y,s(z)))" ),
    Seq( "Suc_0" -> hof"R(s(n),s(m),0)" ) )
  val deltaBc6 = Lemma( esdeltaBc6 ) {
    allL( "Ant_2", le"n:nat" )
    allL( "Ant_2_0", le"(s m:nat)" )
    orL
    negL
    forget( "Suc_0" )
    ref( "phi" )
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"delta (s n) (s m) 0", deltaBc6 )
}
