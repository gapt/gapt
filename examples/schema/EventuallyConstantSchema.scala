package gapt.examples

import gapt.expr._
import gapt.proofs.Sequent
import gapt.proofs.context.Context
import gapt.proofs.context.update.InductiveType
import gapt.proofs.context.update.{ PrimitiveRecursiveFunction => PrimRecFun }
import gapt.proofs.context.update.ProofDefinitionDeclaration
import gapt.proofs.context.update.ProofNameDeclaration
import gapt.proofs.context.update.Sort
import gapt.proofs.gaptic.TacticsProof
import gapt.proofs.gaptic._

object EventuallyConstantSchema extends TacticsProof {
  ctx += InductiveType( "nat", hoc"0 : nat", hoc"s : nat>nat" )
  ctx += Sort( "i" )
  ctx += hoc"f:i>nat"
  ctx += hoc"g:i>i"
  ctx += hoc"z:i"
  ctx += hoc"E: nat>nat>o"
  ctx += hoc"LE: nat>nat>o"
  ctx += hoc"LEQ: nat>nat>o"
  ctx += hoc"iLEQ: i>i>o"

  ctx += hoc"omega: nat>nat"
  ctx += hoc"phi: nat>nat"
  ctx += PrimRecFun( hoc"POR:nat>i>o", "POR 0 x = E 0 (f x) ", "POR (s y) x = (E (s y) (f x) ∨ POR y x)" )
  ctx += "UpBound" -> hos"POR(n,a) :- LE(f(a), s(n))"
  ctx += "gEq" -> hos"E(n,f(a)),E(n,f(g(a))) :- E(f(a), f(g(a)))"
  ctx += "smallest" -> hos"LE(n,0) :- "
  ctx += "reflex" -> hos" :- iLEQ(a,a)"
  ctx += "ordcon" -> hos"LE(f(a),s(n)),iLEQ(a,b) :- E(n,f(b)), LE(f(b),n)"

  val esOmega = Sequent(
    Seq( hof"!x POR(n,x)" ),
    Seq( hof"?x (iLEQ(x,g(x)) -> E(f(x), f(g(x))) )" ) )
  ctx += ProofNameDeclaration( le"omega n", esOmega )
  val esPhi = Sequent(
    Seq( hof"?x !y ((iLEQ(x,y) -> E(n,f(y))) | LE(f(y),n))" ),
    Seq( hof"?x (iLEQ(x,g(x)) -> E(f(x), f(g(x))) )" ) )
  ctx += ProofNameDeclaration( le"phi n", esPhi )

  //The base case of  omega
  val esOmegaBc =
    Sequent(
      Seq( "Ant_0" -> hof"!x POR(0,x)" ),
      Seq( "Suc_0" -> hof"?x (iLEQ(x,g(x)) -> E(f(x), f(g(x))))" ) )
  val omegaBc = Lemma( esOmegaBc ) {
    cut( "cut", hof"?x !y ((iLEQ(x,y) -> E(0,f(y))) | LE(f(y),0))" ) right ref( "phi" )
    exR( "cut", hoc"z" )
    allR( "cut_0", fov"a" )
    orR
    impR
    allL( "Ant_0", fov"a" )
    unfold( "POR" ) atMost 1 in "Ant_0_0"
    trivial
  }
  ctx += ProofDefinitionDeclaration( le"omega 0", omegaBc )
  val esOmegaSc =
    Sequent(
      Seq( "Ant_0" -> hof"!x POR(s(n),x)" ),
      Seq( "Suc_0" -> hof"?x (iLEQ(x,g(x)) -> E(f(x), f(g(x))))" ) )
  val omegaSc = Lemma( esOmegaSc ) {
    cut( "cut", hof"?x !y ((iLEQ(x,y) -> E(s(n),f(y))) | LE(f(y),s(n)))" ) right ref( "phi" )
    exR( "cut", hoc"z" )
    allR( "cut_0", fov"a" )
    orR
    impR
    allL( "Ant_0", fov"a" )
    unfold( "POR" ) atMost 1 in "Ant_0_0"
    orL left trivial; foTheory
  }
  ctx += ProofDefinitionDeclaration( le"omega (s n)", omegaSc )
  val esPhiBc =
    Sequent(
      Seq( "Ant_0" -> hof"?x !y ((iLEQ(x,y) -> E(0,f(y))) | LE(f(y),0))" ),
      Seq( "Suc_0" -> hof"?x (iLEQ(x,g(x)) -> E(f(x), f(g(x))) )" ) )
  val phiBc = Lemma( esPhiBc ) {
    exL( fov"a" )
    allL( fov"a" )
    allL( le"(g a)" )
    exR( fov"a" )
    impR
    orL( "Ant_0_0" ) right foTheory
    orL( "Ant_0_1" ) right foTheory

    impL( "Ant_0_0" )
    by {
      impL( "Ant_0_1" ) left foTheory
      foTheory
    }
    by {
      impL( "Ant_0_1" ) left trivial
      foTheory
    }
  }
  ctx += ProofDefinitionDeclaration( le"phi 0", phiBc )
  val esPhiSc =
    Sequent(
      Seq( "Ant_0" -> hof"?x !y ((iLEQ(x,y) -> E(s(n),f(y))) | LE(f(y),s(n)))" ),
      Seq( "Suc_0" -> hof"?x (iLEQ(x,g(x)) -> E(f(x), f(g(x))) )" ) )
  val phiSc = Lemma( esPhiSc ) {
    cut( "cut", hof"?x !y ((iLEQ(x,y) -> E(n,f(y))) | LE(f(y),n))" ) right ref( "phi" )
    cut( "cut1", hof"?x !y ( iLEQ(x,y) -> E(s(n),f(y)) )" ) left by {
      cut( "cut2", hof"?x ( LE(f(x),s(n)) )" ) left by {
        forget( "cut" )
        exL( fov"a" )
        exR( "cut1", fov"a" )
        allR( "cut1_0", fov"b" )
        allL( fov"b" )
        exR( "cut2", fov"b" )
        prop
      }
      by {
        exL( "cut2", fov"a" )
        exR( "cut", fov"a" )
        allR( fov"b" )
        orR
        impR
        foTheory
      }
    }

    exL( "cut1", fov"a" )
    allL( fov"a" )
    allL( le"(g a)" )
    exR( "Suc_0", fov"a" )
    impL( "cut1_1" ) left {
      impL onAll by { impR; trivial }
    }
    impL( "cut1_0" ) left foTheory
    impR
    foTheory
  }
  ctx += ProofDefinitionDeclaration( le"phi (s n)", phiSc )

}