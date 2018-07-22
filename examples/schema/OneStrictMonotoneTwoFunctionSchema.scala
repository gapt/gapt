package gapt.examples

import gapt.expr._
import gapt.proofs.Context._
import gapt.proofs.Context
import gapt.proofs.Sequent
import gapt.proofs.gaptic._

object OneStrictMonotoneTwoFunctionSchema extends TacticsProof {
  ctx += Context.InductiveType( "nat", hoc"0 : nat", hoc"s : nat>nat" )
  ctx += Context.Sort( "i" )
  ctx += Context.Sort( "name" )
  ctx += hoc"A:name"
  ctx += hoc"B:name"
  ctx += hoc"f:name>i>nat"
  ctx += hoc"suc:i>i"
  ctx += hoc"z:i"
  ctx += hoc"E: nat>nat>o"
  ctx += hoc"LE: nat>nat>o"

  ctx += hoc"omega: nat>nat"
  ctx += hoc"phi: nat>nat"
  ctx += PrimRecFun( hoc"POR:nat>i>name>o", "POR 0 x w = E 0 (f w x) ", "POR (s y) x w = (E (s y) (f w x) ∨ POR y x w)" )
  ctx += "LEDefinition" -> hos"POR(n,a,w) :- LE(f(w,a), s(n))"
  ctx += "LEDefinition2" -> hos"POR(n,suc(a),w) :- LE(f(w,a), s(n))"
  ctx += "LEDefinition3" -> hos"POR(n,a,w) :- LE(f(w,suc(a)), s(n))"

  ctx += "NumericTransitivity" -> hos"E(n,f(w,a)),E(n,f(w,suc(a))) :- E(f(w,a),f(w,suc(a)))"
  ctx += "FunctionRelation" -> hos"E(n, f(A,a)),E(n, f(B, b)),POR(n,suc(b),B) :- LE(f(A, suc(a)), f(B, b))"
  ctx += "FunctionRelation2" -> hos"E(s(n), f(A, a)), POR(n,b,B) :- LE(f(A, suc(a)), f(B, b))"
  ctx += "FunctionRelation3" -> hos"  POR(n,a,A),  POR(n,b,B) :- LE(f(A, suc(a)), f(B, b))"
  ctx += "FunctionRelation4" -> hos"  E(n, f(B, a)),   E(n, f(B, suc(a))) :- LE(f(A, suc(a)), n)"
  ctx += "FunctionRelation5" -> hos"  E(0, f(A, z)) ,E(0, f(A, suc(z)))  :- LE(f(A, b), f(B, a))"

  ctx += "minimalElement" -> hos"LE(f(w,z),0) :- "
  ctx += "ordcon" -> hos"LE(f(w,a),s(n)) :- E(n,f(w,a)), LE(f(w,a),n)"
  ctx += "ordcon2" -> hos"LE(f(w,suc(a)),s(n)) :- E(n,f(w,suc(a))), LE(f(w,a),n)"

  val esOmega = Sequent(
    Seq( hof"!x POR(n,x,A)", hof"!x POR(n,x,B)", hof"!x LE(0 , f(B,x))" ),
    Seq( hof"?x?y (E(f(A,x), f(A,suc(x))) & E(f(B,y), f(B,suc(y))) &  LE(f(A,x), f(B,y)))" ) )
  ctx += Context.ProofNameDeclaration( le"omega n", esOmega )
  val esPhi = Sequent(
    Seq(
      hof"(?x!y( E(n,f(A,x)) & E(n,f(A,suc(x))) & LE(f(A,suc(x)),f(B,y))) | !y (LE(f(A,y),n)))",
      hof"(?x ( E(n,f(B,x)) & E(n,f(B,suc(x))) & LE(f(A,suc(x)),n) ) | !y (LE(f(B,y),n) | LE(f(A,y),f(B,y)) ))" ),
    Seq( hof"?x?y (E(f(A,x), f(A,suc(x))) & E(f(B,y), f(B,suc(y))) &  LE(f(A,x), f(B,y)))" ) )
  ctx += Context.ProofNameDeclaration( le"phi n", esPhi )

  //The base case of  omega
  val esOmegaBc =
    Sequent(
      Seq(
        "Ant_0" -> hof"!x POR(0,x,A)",
        "Ant_1" -> hof"!x POR(0,x,B)" ),
      Seq( "Suc_0" -> hof"?x?y (E(f(A,x), f(A,suc(x))) & E(f(B,y), f(B,suc(y))) & LE(f(A,x), f(B,y)))" ) )
  val omegaBc = Lemma( esOmegaBc ) {
    cut( "cut", hof"(?x!y( E(0,f(A,x)) & E(0,f(A,suc(x))) & LE(f(A,suc(x)),f(B,y))) | !y (LE(f(A,y),0))) & (?x ( E(0,f(B,x)) & E(0,f(B,suc(x))) & LE(f(A,suc(x)),0) ) | !y (LE(f(B,y),0) | LE(f(A,y),f(B,y)) ))" )
    andR
    orR
    exR( "cut_0", hoc"z" )
    allR( "cut_0_0", fov"a" )
    andR
    andR
    allL( "Ant_0", hoc"z" )
    unfold( "POR" ) atMost 1 in "Ant_0_0"
    trivial
    allL( "Ant_0", le"(suc z)" )
    unfold( "POR" ) atMost 1 in "Ant_0_0"
    trivial
    allL( "Ant_0", hoc"z" )
    allL( "Ant_0", le"(suc z)" )
    unfold( "POR" ) atMost 1 in "Ant_0_0"
    unfold( "POR" ) atMost 1 in "Ant_0_1"
    ref( "FunctionRelation5" )
    orR
    exR( "cut_0", hoc"z" )
    andR
    andR
    allL( "Ant_1", hoc"z" )
    unfold( "POR" ) atMost 1 in "Ant_1_0"
    trivial
    allL( "Ant_1", le"(suc z)" )
    unfold( "POR" ) atMost 1 in "Ant_1_0"
    trivial
    allR( "cut_1", fov"a" )
    orR
    allL( "Ant_0", hoc"z" )
    unfold( "POR" ) atMost 1 in "Ant_0_0"
    allL( "Ant_0", le"(suc z)" )
    unfold( "POR" ) atMost 1 in "Ant_0_1"
    ref( "FunctionRelation5" )
    andL
    ref( "phi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"omega 0", omegaBc )
  val esOmegaSc =
    Sequent(
      Seq(
        "Ant_0" -> hof"!x POR(s(n),x,A)",
        "Ant_1" -> hof"!x POR(s(n),x,B)" ),
      Seq( "Suc_0" -> hof"?x?y (E(f(A,x), f(A,suc(x))) & E(f(B,y), f(B,suc(y))) & LE(f(A,x), f(B,y)))" ) )
  val omegaSc = Lemma( esOmegaSc ) {
    cut( "cut", hof"(?x!y( E(s(n),f(A,x)) & E(s(n),f(A,suc(x))) & LE(f(A,suc(x)),f(B,y))) | !y (LE(f(A,y),s(n)))) & (?x ( E(s(n),f(B,x)) & E(s(n),f(B,suc(x))) & LE(f(A,suc(x)),s(n)) ) | !y (LE(f(B,y),s(n)) | LE(f(A,y),f(B,y)) ))" )
    andR( "cut" )
    orR( "cut" )
    allR( "cut_1", fov"a" )
    exR( "cut_0", fov"a" )
    allR( "cut_0_0", fov"b" )
    andR( "cut_0_0" )
    allL( "Ant_0", fov"a" )
    unfold( "POR" ) atMost 1 in "Ant_0_0"
    orL
    andR
    trivial
    allL( "Ant_0", le"(suc a)" )
    unfold( "POR" ) atMost 1 in "Ant_0_1"
    orL
    trivial
    ref( "LEDefinition2" )
    ref( "LEDefinition" )
    allL( "Ant_0", fov"a" )
    allL( "Ant_1", fov"b" )
    unfold( "POR" ) atMost 1 in "Ant_0_0"
    unfold( "POR" ) atMost 1 in "Ant_1_0"
    orL( "Ant_1_0" )
    orL( "Ant_0_0" )
    allL( "Ant_1", le"(suc b)" )
    ref( "FunctionRelation" )
    ref( "LEDefinition" )
    orL( "Ant_0_0" )
    ref( "FunctionRelation2" )
    ref( "FunctionRelation3" )
    orR( "cut" )
    allR( fov"a" )
    exR( "cut_0", fov"a" )
    orR( "cut_1" )
    allL( "Ant_1", fov"a" )
    unfold( "POR" ) atMost 1 in "Ant_1_0"
    orL
    andR
    andR
    trivial
    allL( "Ant_1", le"(suc a)" )
    unfold( "POR" ) atMost 1 in "Ant_1_1"
    orL
    trivial
    ref( "LEDefinition2" )
    allL( "Ant_1", le"(suc a)" )
    unfold( "POR" ) atMost 1 in "Ant_1_1"
    orL
    ref( "FunctionRelation4" )
    ref( "LEDefinition2" )
    ref( "LEDefinition" )
    andL
    ref( "phi" )
    /*allL( "Ant_0", fov"a" )
    unfold( "POR" ) atMost 1 in "Ant_0_0"
    orL
    allL( "Ant_1", fov"a" )
    unfold( "POR" ) atMost 1 in "Ant_1_0"
    orL
    trivial
    ref( "FunctionRelation5" )
    allL( "Ant_1", le"(suc a)" )
    unfold( "POR" ) atMost 1 in "Ant_1_0"
    orL
    trivial
    ref( "FunctionRelation6" )
    allL( "Ant_1", le"(suc a)" )
    ref( "FunctionRelation7" )
    ref( "LEDefinition3" )
    andL
    ref( "phi" )*/
  }
  ctx += Context.ProofDefinitionDeclaration( le"omega (s n)", omegaSc )

  /*val esPhiBc =
    Sequent(
      Seq(
        "Ant_0" -> hof"?x !y ( E(0,f(A,x)) & E(0,f(A,suc(x))) & LE(f(A,x),f(B,y)) ) | !y (LE(f(A,y),0))",
        "Ant_1" -> hof"?x   ( E(0,f(B,x)) & E(0,f(B,suc(x))) & LE(f(A,x),0)) | !y (LE(f(B,y),0) & LE(f(A,y),0))" ),
      Seq( "Suc_0" -> hof"?x?y (E(f(A,x), f(A,suc(x))) & E(f(B,y), f(B,suc(y))) &  LE(f(A,x), f(B,y)))" ) )
  val phiBc = Lemma( esPhiBc ) {
    orL( "Ant_0" )
    orL( "Ant_1" )
    exL( "Ant_0", fov"a" )
    exL( "Ant_1", fov"b" )
    andL( "Ant_0" )
    andL( "Ant_1" )
    exR( fov"a" )
    exR( "Suc_0_0", fov"b" )
    andR
    andR
    ref( "NumericTransitivity" )
    ref( "NumericTransitivity" )

  }
  ctx += Context.ProofDefinitionDeclaration( le"phi 0", phiBc )

  val esPhiSc =
    Sequent(
      Seq( "Ant_0" -> hof"?x ( E(s(n),f(x)) & E(s(n),f(suc(x)))) | !y (LE(f(y),s(n)))" ),
      Seq( "Suc_0" -> hof"?x (E(f(x), f(suc(x))) )" ) )
  val phiSc = Lemma( esPhiSc ) {
    cut( "cut", hof"?x ( E(n,f(x)) & E(n,f(suc(x)))) | !y (LE(f(y),n))" )
    orR
    orL
    exL( fov"a" )
    andL
    exR( "Suc_0", fov"a" )
    ref( "NumericTransitivity" )
    allR( fov"b" )
    exR( "cut_0", fov"b" )
    allL( fov"b" )
    andR
    ref( "ordcon" )
    allL( le"(suc b)" )
    ref( "ordcon2" )
    ref( "phi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi (s n)", phiSc )
*/
}

