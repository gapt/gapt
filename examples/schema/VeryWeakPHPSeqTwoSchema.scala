package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.PrimRecFun
import at.logic.gapt.proofs.{ Context, Sequent }
import at.logic.gapt.proofs.gaptic.TacticsProof
import at.logic.gapt.proofs.gaptic._

object VeryWeakPHPSeqTwoSchema extends TacticsProof {
  ctx += Context.InductiveType( "nat", hoc"0 : nat", hoc"s : nat>nat" )
  ctx += Context.Sort( "i" )
  ctx += hoc"f:nat>i>nat"
  ctx += hoc"suc:i>i"
  ctx += hoc"z:i"
  ctx += hoc"E: nat>nat>o"
  ctx += hoc"LE: nat>nat>o"
  ctx += hoc"omega: nat>nat"
  ctx += hoc"phi: nat>nat"

  ctx += PrimRecFun( hoc"POR:nat>nat>i>o", "POR 0 m x = E 0 (f m x) ", "POR (s y) m x = (E (s y) (f m x) ∨ POR y m x)" )
  ctx += PrimRecFun( hoc"PAND:nat>nat>o", "(PAND 0 n)= (∀x (POR n 0 x))", "(PAND (s m) n) = ((∀x (POR n (s m) x)) & (PAND m n))" )
  ctx += PrimRecFun( hoc"TopFuncDef:nat>nat>i>o", "(TopFuncDef 0 k x)= (E (f 0 x) (f k x)) ", "(TopFuncDef (s m) k x)= ((E (f (s m) x) (f k x)) | (TopFuncDef m k x))" )
  ctx += PrimRecFun(
    hoc"CutDistinct:nat>nat>o",
    "(CutDistinct 0 n) =  ( (∃x ((E n (f 0 x)) & (E n (f 0 (suc x)))) ) | (∀y (LE (f 0 y) n)))",
    "(CutDistinct (s m) n ) = (" +
      "(CutDistinct m n) & ( (∃x ((E n (f (s m) x)) & (E n (f (s m) (suc x)))) ) | (∀y (LE (f (s m) y) n)))" +
      ")" )
  ctx += "LEDefinition" -> hos"POR(n,m,a) :- LE(f(m,a), s(n))"
  ctx += "LEDefinition2" -> hos"POR(n,m, suc(a)) :- LE(f(m,a), s(n))"
  ctx += "NumericTransitivity" -> hos"E(n,f(m,a)),E(n,f(m,suc(a))) :- E(f(m,a), f(m,suc(a)))"
  ctx += "TransitivityE" -> hos"E(a,b),E(b,c) :- E(a,c)"
  ctx += "StrongTransitivityE0" -> hos"E(a,f(0,b)),E(a,f(0,suc(b))),E(f(0,c),f(s(s(0)),d)) :- E(a,f(s(s(0)),d))"
  ctx += "StrongTransitivityE1" -> hos"E(a,f(s(0),b)),E(a,f(s(0),suc(b))),E(f(s(0),c),f(s(s(0)),d)) :- E(a,f(s(s(0)),d))"
  ctx += "minimalElement" -> hos"LE(f(m,a),0) :- "
  ctx += "ordcon" -> hos"LE(f(m,a),s(n)) :- E(n,f(k,a)), LE(f(k,a),n)"
  ctx += "ordcon2" -> hos"LE(f(m,suc(a)),s(n)) :- E(n,f(k,suc(a))), LE(f(k,a),n)"

  val esOmega = Sequent(
    Seq(
      hof"PAND(s(0),n)",
      hof"!x TopFuncDef(s(0),s(s(0)),x)" ),
    Seq( hof"?x ( E(f(s(s(0)),x), f(s(s(0)),suc(x))) )" ) )
  ctx += Context.ProofNameDeclaration( le"omega n", esOmega )
  val esPhi = Sequent(
    Seq(
      hof" CutDistinct(s(0),n)",
      hof"!x TopFuncDef(s(0),s(s(0)),x)" ),
    Seq( hof"?x ( E(f(s(s(0)),x), f(s(s(0)),suc(x))) )" ) )
  ctx += Context.ProofNameDeclaration( le"phi n", esPhi )

  //The base case of omega
  val esOmegaBc =
    Sequent(
      Seq(
        "Ant_0" -> hof"PAND(s(0),0)",
        "Ant_1" -> hof"!x TopFuncDef(s(0),s(s(0)),x)" ),
      Seq( "Suc_0" -> hof"?x (E(f(s(s(0)),x), f(s(s(0)),suc(x))))" ) )
  val omegaBc = Lemma( esOmegaBc ) {
    cut( "cut", hof"CutDistinct(s(0),0)" )
    unfold( "CutDistinct" ) atMost 1 in "cut"
    unfold( "PAND" ) atMost 1 in "Ant_0"
    andL
    unfold( "PAND" ) atMost 1 in "Ant_0_1"
    andR
    unfold( "CutDistinct" ) atMost 1 in "cut"
    orR
    exR( "cut_0", le"z" )
    allL( "Ant_0_1", le"z" )
    allL( "Ant_0_1", le"(suc z)" )
    unfold( "POR" ) atMost 1 in "Ant_0_1_0"
    unfold( "POR" ) atMost 1 in "Ant_0_1_1"
    andR
    trivial
    trivial
    orR
    exR( "cut_0", le"z" )
    allL( "Ant_0_0", le"z" )
    allL( "Ant_0_0", le"(suc z)" )
    unfold( "POR" ) atMost 1 in "Ant_0_0_0"
    unfold( "POR" ) atMost 1 in "Ant_0_0_1"
    andR
    trivial
    trivial
    ref( "phi" )

  }
  ctx += Context.ProofDefinitionDeclaration( le"omega 0", omegaBc )

  //The base case of omega
  val esOmegaSc =
    Sequent(
      Seq(
        "Ant_0" -> hof"PAND(s(0),s(n))",
        "Ant_1" -> hof"!x TopFuncDef(s(0),s(s(0)),x)" ),
      Seq( "Suc_0" -> hof"?x (E(f(s(s(0)),x), f(s(s(0)),suc(x))))" ) )
  val OmegaSc = Lemma( esOmegaSc ) {
    cut( "cut", hof"CutDistinct(s(0),s(n))" )
    unfold( "CutDistinct" ) atMost 1 in "cut"
    unfold( "PAND" ) atMost 1 in "Ant_0"
    andL
    unfold( "PAND" ) atMost 1 in "Ant_0_1"
    andR
    unfold( "CutDistinct" ) atMost 1 in "cut"
    orR
    allR( "cut_1", fov"a" )
    exR( "cut_0", le"a" )
    allL( "Ant_0_1", le"a" )
    allL( "Ant_0_1", le"(suc a)" )
    unfold( "POR" ) atMost 1 in "Ant_0_1_0"
    unfold( "POR" ) atMost 1 in "Ant_0_1_1"
    orL( "Ant_0_1_0" )
    orL
    andR
    trivial
    trivial
    ref( "LEDefinition2" )
    ref( "LEDefinition" )

    orR
    allR( "cut_1", fov"a" )
    exR( "cut_0", le"a" )
    allL( "Ant_0_0", le"a" )
    allL( "Ant_0_0", le"(suc a)" )
    unfold( "POR" ) atMost 1 in "Ant_0_0_0"
    unfold( "POR" ) atMost 1 in "Ant_0_0_1"
    orL( "Ant_0_0_0" )
    orL
    andR
    trivial
    trivial
    ref( "LEDefinition2" )
    ref( "LEDefinition" )
    ref( "phi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"omega (s n)", OmegaSc )

  val esPhiBc3 =
    Sequent(
      Seq(
        "Ant_0" -> hof"CutDistinct(s(0),0)",
        "Ant_1" -> hof"!x TopFuncDef(s(0),s(s(0)),x)" ),
      Seq( "Suc_0" -> hof"?x (E(f(s(s(0)),x), f(s(s(0)),suc(x))) )" ) )
  val phiBc3 = Lemma( esPhiBc3 ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_0"
    andL
    orL
    exL( fov"a" )
    andL
    allL( fov"a" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_0"
    orL
    allL( le"(suc a)" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
    orL
    cut( "cut2", hof"E(0, f((s (s 0)),a))" )
    ref( "TransitivityE" )
    cut( "cut1", hof"E(0, f((s (s 0)),(suc a)))" )
    ref( "TransitivityE" )
    exR( fov"a" )
    ref( "NumericTransitivity" )
    cut( "cut2", hof"E(0, f((s (s 0)),a))" )
    ref( "TransitivityE" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
    unfold( "CutDistinct" ) atMost 1 in "Ant_0_0"
    orL
    exL( fov"b" )
    andL
    exR( fov"a" )
    cut( "cut1", hof"E(0, f((s (s 0)),(suc a)))" )
    ref( "StrongTransitivityE0" )
    ref( "NumericTransitivity" )
    allL( "Ant_0_0", fov"a" )
    ref( "minimalElement" )
    unfold( "CutDistinct" ) atMost 1 in "Ant_0_0"
    orL
    exL( fov"b" )
    andL
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_0"
    cut( "cut1", hof"E(0, f((s (s 0)),a))" )
    ref( "StrongTransitivityE0" )
    allL( "Ant_1", le"(suc a)" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
    orL
    cut( "cut1", hof"E(0, f((s (s 0)),(suc a)))" )
    ref( "TransitivityE" )
    exR( fov"a" )
    ref( "NumericTransitivity" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
    cut( "cut1", hof" E(0, f((s (s 0)),(suc a)))" )
    ref( "StrongTransitivityE0" )
    exR( fov"a" )
    ref( "NumericTransitivity" )
    allL( "Ant_0_0", le" a" )
    ref( "minimalElement" )
    allL( "Ant_0_1", le" a" )
    ref( "minimalElement" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi 0", phiBc3 )

  val esPhiSc =
    Sequent(
      Seq(
        "Ant_0" -> hof"CutDistinct(s(0),s(n))",
        "Ant_1" -> hof"!x TopFuncDef(s(0),s(s(0)),x)" ),
      Seq( "Suc_0" -> hof"?x (E(f(s(s(0)),x), f(s(s(0)),suc(x))) )" ) )
  val phiSc = Lemma( esPhiSc ) {
    cut( "cut", hof"CutDistinct(s(0),n)" )
    unfold( "CutDistinct" ) atMost 1 in "Ant_0"
    unfold( "CutDistinct" ) atMost 1 in "cut"
    andL
    andR
    unfold( "CutDistinct" ) atMost 1 in "Ant_0_0"
    unfold( "CutDistinct" ) atMost 1 in "cut"
    orR
    allR( fov"a" )
    orL( "Ant_0_0" )
    orL( "Ant_0_1" )
    exL( "Ant_0_0", fov"b" )
    exL( "Ant_0_1", fov"c" )
    exR( "Suc_0", fov"b" )
    andL( "Ant_0_0" )
    andL( "Ant_0_1" )
    allL( "Ant_1", fov"b" )
    allL( "Ant_1", le"(suc b)" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_0"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
    orL( "Ant_1_0" )
    orL( "Ant_1_1" )
    cut( "cut1", hof"E(s(n), f((s (s 0)),b))" )
    ref( "StrongTransitivityE1" )
    cut( "cut1", hof"E(s(n), f((s (s 0)),(suc b)))" )
    ref( "StrongTransitivityE1" )
    ref( "NumericTransitivity" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
    cut( "cut1", hof"E(s(n), f((s (s 0)),b))" )
    ref( "StrongTransitivityE1" )
    cut( "cut2", hof"E(s(n), f((s (s 0)),(suc b)))" )
    ref( "TransitivityE" )
    ref( "NumericTransitivity" )
    orL
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_0"
    cut( "cut1", hof"E(s(n), f((s (s 0)),b))" )
    ref( "TransitivityE" )
    cut( "cut2", hof"E(s(n), f((s (s 0)),(suc b)))" )
    ref( "StrongTransitivityE1" )
    ref( "NumericTransitivity" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_0"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
    cut( "cut1", hof"E(s(n), f((s (s 0)),b))" )
    ref( "TransitivityE" )
    cut( "cut2", hof"E(s(n), f((s (s 0)),(suc b)))" )
    ref( "TransitivityE" )
    ref( "NumericTransitivity" )
    allL( "Ant_0_1", fov"a" )
    exR( "cut_0", fov"a" )
    andR
    ref( "ordcon" )
    allL( "Ant_0_1", le"(suc a)" )
    ref( "ordcon2" )
    allL( "Ant_0_0", fov"a" )
    exR( "cut_0", fov"a" )
    andR
    ref( "ordcon" )
    allL( "Ant_0_0", le"(suc a)" )
    ref( "ordcon2" )
    unfold( "CutDistinct" ) atMost 1 in "Ant_0_0"
    orR
    allR( "cut_1", fov"a" )
    exR( "cut_0", fov"a" )
    orL( "Ant_0_0" )
    orL( "Ant_0_1" )
    exL( "Ant_0_0", fov"d" )
    andL
    exL( "Ant_0_1", fov"e" )
    andL
    exR( "Suc_0", fov"d" )
    allL( "Ant_1", fov"d" )
    allL( "Ant_1", le"(suc d)" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_0"
    orL
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
    orL
    cut( "cut1", hof"E(s(n), f((s (s 0)),d))" )
    ref( "StrongTransitivityE1" )
    cut( "cut1", hof"E(s(n), f((s (s 0)),(suc d)))" )
    ref( "StrongTransitivityE1" )
    ref( "NumericTransitivity" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
    cut( "cut1", hof"E(s(n), f((s (s 0)),d))" )
    ref( "StrongTransitivityE1" )
    cut( "cut2", hof"E(s(n), f((s (s 0)),(suc d)))" )
    ref( "TransitivityE" )
    ref( "NumericTransitivity" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
    orL
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_0"
    cut( "cut1", hof"E(s(n), f((s (s 0)),d))" )
    ref( "TransitivityE" )
    cut( "cut2", hof"E(s(n), f((s (s 0)),(suc d)))" )
    ref( "StrongTransitivityE1" )
    ref( "NumericTransitivity" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_0"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
    cut( "cut1", hof"E(s(n), f((s (s 0)),d))" )
    ref( "TransitivityE" )
    cut( "cut2", hof"E(s(n), f((s (s 0)),(suc d)))" )
    ref( "TransitivityE" )
    ref( "NumericTransitivity" )
    allL( "Ant_0_1", fov"a" )
    andR
    ref( "ordcon" )
    allL( "Ant_0_1", le"(suc a)" )
    ref( "ordcon2" )
    allL( "Ant_0_0", fov"a" )
    andR
    ref( "ordcon" )
    allL( "Ant_0_0", le"(suc a)" )
    ref( "ordcon2" )
    forget( "Ant_0" )
    ref( "phi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi (s n)", phiSc )

}

