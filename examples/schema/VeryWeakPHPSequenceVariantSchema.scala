package gapt.examples

import gapt.expr._
import gapt.proofs.Context._
import gapt.proofs.Context
import gapt.proofs.Sequent
import gapt.proofs.gaptic._

object VeryWeakPHPSequenceVariantSchema extends TacticsProof {
  ctx += Context.InductiveType( "nat", hoc"0 : nat", hoc"s : nat>nat" )
  ctx += Context.Sort( "i" )
  ctx += hoc"f:nat>i>nat"
  ctx += hoc"suc:i>i"
  ctx += hoc"z:i"
  ctx += hoc"E: nat>nat>o"
  ctx += hoc"LE: nat>nat>o"
  ctx += hoc"omega: nat>nat>nat"
  ctx += hoc"gamma: nat>nat>nat"
  ctx += hoc"phi: nat>nat>nat"
  ctx += hoc"mu: nat>nat>nat>nat"
  ctx += hoc"epsilon: nat>nat>i>nat"
  ctx += hoc"epsilon2: nat>nat>i>nat"
  ctx += hoc"epsilon3:  nat>nat>i>nat"
  ctx += hoc"epsilon4:  nat>nat>nat>i>nat"
  ctx += hoc"epsilon5:  nat>nat>nat>i>nat"
  ctx += hoc"epsilon6:  nat>nat>nat>i>nat"
  ctx += hoc"theta: nat>nat>nat>nat>i>i>nat"
  ctx += hoc"theta2: nat>nat>nat>nat>i>i>nat"
  ctx += hoc"theta3: nat>nat>nat>nat>i>i>nat"
  ctx += hoc"pi: nat>nat>nat>nat"

  ctx += PrimRecFun( hoc"POR:nat>nat>i>o", "POR 0 m x = E 0 (f m x) ", "POR (s y) m x = (E (s y) (f m x) ∨ POR y m x)" )
  ctx += PrimRecFun( hoc"PAND:nat>nat>o", "(PAND 0 n)= (∀x (POR n 0 x))", "(PAND (s m) n) = ((∀x (POR n (s m) x)) | (PAND m n))" )
  ctx += PrimRecFun( hoc"TopFuncDef:nat>nat>i>o", "(TopFuncDef 0 k x)= (E (f 0 x) (f k x)) ", "(TopFuncDef (s m) k x)= ((E (f (s m) x) (f k x)) | (TopFuncDef m k x))" )
  ctx += PrimRecFun(
    hoc"CutDistinct:nat>nat>o",
    "(CutDistinct 0 n) =  ( (∃x ((E n (f 0 x)) & (E n (f 0 (suc x)))) ) | (∀y (LE (f 0 y) n)))",
    "(CutDistinct (s m) n ) = (" +
      "(CutDistinct m n) | ( (∃x ((E n (f (s m) x)) & (E n (f (s m) (suc x)))) ) | (∀y (LE (f (s m) y) n)))" +
      ")" )
  ctx += "LEDefinition" -> hos"POR(n,m,a) :- LE(f(m,a), s(n))"
  ctx += "LEDefinition2" -> hos"POR(n,m, suc(a)) :- LE(f(m,a), s(n))"
  ctx += "NumericTransitivity" -> hos"E(n,f(m,a)),E(n,f(m,suc(a))) :- E(f(m,a), f(m,suc(a)))"
  ctx += "TransitivityE" -> hos"E(a,b),E(b,c) :- E(a,c)"
  ctx += "StrongTransitivityE" -> hos"E(a,f(m,b)),E(a,f(m,suc(b))),E(f(m,c),f(k,d)) :- E(a,f(k,d))"
  ctx += "minimalElement" -> hos"LE(f(m,a),0) :- "
  ctx += "ordcon" -> hos"LE(f(m,a),s(n)) :- E(n,f(w,a)), LE(f(w,a),n)"
  ctx += "ordcon2" -> hos"LE(f(m,suc(a)),s(n)) :- E(n,f(w,suc(a))), LE(f(w,a),n)"

  val esOmega = Sequent(
    Seq(
      hof"PAND(m,n)",
      hof"!x TopFuncDef(m,s(m),x)" ),
    Seq( hof"?x ( E(f(s(m),x), f(s(m),suc(x))) )" ) )
  ctx += Context.ProofNameDeclaration( le"omega n m", esOmega )
  val esGamma = Sequent(
    Seq( hof"PAND(m,n)" ),
    Seq( hof"CutDistinct(m,n)" ) )
  ctx += Context.ProofNameDeclaration( le"gamma n m", esGamma )
  val esPhi = Sequent(
    Seq(
      hof" CutDistinct(m,n)",
      hof"!x TopFuncDef(m,s(m),x)" ),
    Seq( hof"?x ( E(f(s(m),x), f(s(m),suc(x))) )" ) )
  ctx += Context.ProofNameDeclaration( le"phi n m", esPhi )
  val esMu = Sequent(
    Seq(
      hof"CutDistinct(m,s(n))",
      hof"!x TopFuncDef(m,k,x)" ),
    Seq(
      hof"?x ( E(f(k,x), f(k,suc(x))) )",
      hof"CutDistinct(m,n)" ) )
  ctx += Context.ProofNameDeclaration( le"mu n m k", esMu )
  val esEpsilon = Sequent(
    Seq(
      hof"E(0, f(k, suc(x)))",
      hof"TopFuncDef(m,k,x)",
      hof"CutDistinct(m,0)" ),
    Seq( hof"E(f(k, x), f(k, suc(x)))" ) )
  ctx += Context.ProofNameDeclaration( le"epsilon m k x", esEpsilon )
  val esEpsilon2 = Sequent(
    Seq(
      hof"E(0, f(k, x))",
      hof"TopFuncDef(m,k,suc(x))",
      hof"CutDistinct(m,0)" ),
    Seq( hof"E(f(k, x), f(k, suc(x)))" ) )
  ctx += Context.ProofNameDeclaration( le"epsilon2 m k x", esEpsilon2 )
  val esEpsilon3 = Sequent(
    Seq(
      hof"TopFuncDef(m,k,x)",
      hof"TopFuncDef(m,k,suc(x))",
      hof"CutDistinct(m,0)" ),
    Seq( hof"E(f(k, x), f(k, suc(x)))" ) )
  ctx += Context.ProofNameDeclaration( le"epsilon3 m k x", esEpsilon3 )
  val esEpsilon4 = Sequent(
    Seq(
      hof"E(s(n), f(k, x))",
      hof"TopFuncDef(m,k,suc(x))",
      hof"CutDistinct(m,s(n))" ),
    Seq(
      hof"E(f(k, x), f(k, suc(x)))",
      hof"CutDistinct(m,n)" ) )
  ctx += Context.ProofNameDeclaration( le"epsilon4 m k n x", esEpsilon4 )
  val esEpsilon5 = Sequent(
    Seq(
      hof"E(s(n), f(k, suc(x)))",
      hof"TopFuncDef(m,k,x)",
      hof"CutDistinct(m,s(n))" ),
    Seq(
      hof"E(f(k, x), f(k, suc(x)))",
      hof"CutDistinct(m,n)" ) )
  ctx += Context.ProofNameDeclaration( le"epsilon5 m k n x", esEpsilon5 )
  val esEpsilon6 = Sequent(
    Seq(
      hof"TopFuncDef(m,k,suc(x))",
      hof"TopFuncDef(m,k,x)",
      hof"CutDistinct(m,s(n))" ),
    Seq(
      hof"E(f(k, x), f(k, suc(x)))",
      hof"CutDistinct(m,n)" ) )
  ctx += Context.ProofNameDeclaration( le"epsilon6 m k n x", esEpsilon6 )
  val esTheta = Sequent(
    Seq(
      hof"E(s(n), f(k, y))",
      hof"TopFuncDef(m,k,suc(y))",
      hof"CutDistinct(m,s(n))" ),
    Seq(
      hof"E(f(k, y), f(k, suc(y)))",
      hof"E(n, f(w, x)) & E(n, f(w, suc(x)))",
      hof"LE(f(w, x), n)" ) )
  ctx += Context.ProofNameDeclaration( le"theta m k w n x y", esTheta )
  val esTheta2 = Sequent(
    Seq(
      hof"E(s(n), f(k, suc(y)))",
      hof"TopFuncDef(m,k,y)",
      hof"CutDistinct(m,s(n))" ),
    Seq(
      hof"E(f(k, y), f(k, suc(y)))",
      hof"E(n, f(w, x)) & E(n, f(w, suc(x)))",
      hof"LE(f(w, x), n)" ) )
  ctx += Context.ProofNameDeclaration( le"theta2 m k w n x y", esTheta2 )
  val esTheta3 = Sequent(
    Seq(
      hof"TopFuncDef(m,k,suc(y))",
      hof"TopFuncDef(m,k,y)",
      hof"CutDistinct(m,s(n))" ),
    Seq(
      hof"E(f(k, y), f(k, suc(y)))",
      hof"E(n, f(w, x)) & E(n, f(w, suc(x)))",
      hof"LE(f(w, x), n)" ) )
  ctx += Context.ProofNameDeclaration( le"theta3 m k w n x y", esTheta3 )
  val espi = Sequent(
    Seq( hof"!x LE(f(k, x), s(n))" ),
    Seq( hof"CutDistinct(m,n)" ) )
  ctx += Context.ProofNameDeclaration( le"pi n m k", espi )
  //The base case of  omega
  val esOmegaBc =
    Sequent(
      Seq(
        "Ant_0" -> hof"PAND(0,0)",
        "Ant_1" -> hof"!x TopFuncDef(0,s(0),x)" ),
      Seq( "Suc_0" -> hof"?x (E(f(s(0),x), f(s(0),suc(x))))" ) )
  val omegaBc = Lemma( esOmegaBc ) {
    cut( "cut", hof"CutDistinct(0,0)" )
    unfold( "CutDistinct" ) atMost 1 in "cut"
    unfold( "PAND" ) atMost 1 in "Ant_0"
    orR
    exR( "cut_0", hoc"z" )
    andR
    allL( "Ant_0", hoc"z" )
    unfold( "POR" ) atMost 1 in "Ant_0_0"
    trivial
    allL( "Ant_0", le"(suc z)" )
    unfold( "POR" ) atMost 1 in "Ant_0_0"
    trivial
    ref( "phi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"omega 0 0", omegaBc )

  //The base case of omega
  val esOmegaBc2 =
    Sequent(
      Seq(
        "Ant_0" -> hof"PAND(s(m),0)",
        "Ant_1" -> hof"!x TopFuncDef(s(m),s(s(m)),x)" ),
      Seq( "Suc_0" -> hof"?x (E(f(s(s(m)),x), f(s(s(m)),suc(x))))" ) )
  val omegaBc2 = Lemma( esOmegaBc2 ) {
    cut( "cut", hof"CutDistinct(s(m),0)" )
    unfold( "CutDistinct" ) atMost 1 in "cut"
    unfold( "PAND" ) atMost 1 in "Ant_0"
    andL
    andR
    ref( "gamma" )
    orR
    allR( fov"a" )
    exR( "cut_0", fov"a" )
    andR
    allL( "Ant_0_0", fov"a" )
    unfold( "POR" ) atMost 1 in "Ant_0_0_0"
    trivial
    allL( "Ant_0_0", le"(suc a)" )
    unfold( "POR" ) atMost 1 in "Ant_0_0_0"
    trivial
    ref( "phi" )

  }
  ctx += Context.ProofDefinitionDeclaration( le"omega 0 (s m)", omegaBc2 )

  val esOmegaBc3 =
    Sequent(
      Seq(
        "Ant_0" -> hof"PAND(0,s(n))",
        "Ant_1" -> hof"!x TopFuncDef(0,s(0),x)" ),
      Seq( "Suc_0" -> hof"?x (E(f(s(0),x), f(s(0),suc(x))))" ) )
  val omegaBc3 = Lemma( esOmegaBc3 ) {
    cut( "cut", hof"CutDistinct(0,s(n))" )
    unfold( "CutDistinct" ) atMost 1 in "cut"
    unfold( "PAND" ) atMost 1 in "Ant_0"
    orR
    allR( "cut_1", fov"a" )
    exR( "cut_0", fov"a" )
    allL( "Ant_0", fov"a" )
    unfold( "POR" ) atMost 1 in "Ant_0_0"
    orL
    allL( "Ant_0", le"(suc a)" )
    unfold( "POR" ) atMost 1 in "Ant_0_1"
    orL
    andR
    trivial
    trivial
    ref( "LEDefinition2" )
    ref( "LEDefinition" )
    ref( "phi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"omega (s n) 0", omegaBc3 )

  //The base case of omega
  val esOmegaSc =
    Sequent(
      Seq(
        "Ant_0" -> hof"PAND(s(m),s(n))",
        "Ant_1" -> hof"!x TopFuncDef(s(m),s(s(m)),x)" ),
      Seq( "Suc_0" -> hof"?x (E(f(s(s(m)),x), f(s(s(m)),suc(x))))" ) )
  val OmegaSc = Lemma( esOmegaSc ) {
    cut( "cut", hof"CutDistinct(s(m),s(n))" )
    unfold( "CutDistinct" ) atMost 1 in "cut"
    unfold( "PAND" ) atMost 1 in "Ant_0"
    andL
    andR
    ref( "gamma" )
    orR
    allR( fov"a" )
    exR( "cut_0", fov"a" )
    andR
    allL( "Ant_0_0", fov"a" )
    unfold( "POR" ) atMost 1 in "Ant_0_0_0"
    orL( "Ant_0_0_0" )
    trivial
    ref( "LEDefinition" )
    allL( "Ant_0_0", le"(suc a)" )
    unfold( "POR" ) atMost 1 in "Ant_0_0_0"
    orL( "Ant_0_0_0" )
    trivial
    ref( "LEDefinition2" )
    ref( "phi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"omega (s n) (s m)", OmegaSc )

  val esGammaBc =
    Sequent(
      Seq( "Ant_0" -> hof"PAND(0,0)" ),
      Seq( "Suc_0" -> hof" CutDistinct(0,0)" ) )
  val gammaBc = Lemma( esGammaBc ) {
    unfold( "CutDistinct" ) atMost 1 in "Suc_0"
    unfold( "PAND" ) atMost 1 in "Ant_0"
    orR
    allR( "Suc_0_1", fov"a" )
    exR( "Suc_0_0", fov"a" )
    unfold( "POR" ) atMost 1 in "Ant_0"
    allL( fov"a" )
    allL( le"(suc a)" )
    andR
    trivial
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"gamma 0 0", gammaBc )
  val esGammaBc2 =
    Sequent(
      Seq( "Ant_0" -> hof"PAND(s(m),0)" ),
      Seq( "Suc_0" -> hof"CutDistinct(s(m),0)" ) )
  val gammaBc2 = Lemma( esGammaBc2 ) {
    unfold( "CutDistinct" ) atMost 1 in "Suc_0"
    unfold( "PAND" ) atMost 1 in "Ant_0"
    andL
    andR
    ref( "gamma" )
    orR
    allR( "Suc_0_1", fov"a" )
    exR( "Suc_0_0", fov"a" )
    unfold( "POR" ) atMost 1 in "Ant_0_0"
    allL( fov"a" )
    allL( le"(suc a)" )
    andR
    trivial
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"gamma 0 (s m)", gammaBc2 )

  val esGammaBc3 =
    Sequent(
      Seq( "Ant_0" -> hof"PAND(0,s(n))" ),
      Seq( "Suc_0" -> hof" CutDistinct(0,s(n))" ) )
  val gammaBc3 = Lemma( esGammaBc3 ) {
    unfold( "CutDistinct" ) atMost 1 in "Suc_0"
    unfold( "PAND" ) atMost 1 in "Ant_0"
    orR
    allR( "Suc_0_1", fov"a" )
    exR( "Suc_0_0", fov"a" )
    unfold( "POR" ) atMost 1 in "Ant_0"
    allL( fov"a" )
    orL
    allL( le"(suc a)" )
    orL
    andR
    trivial
    trivial
    allL( le"(suc a)" )
    orL
    andR
    trivial
    trivial
    ref( "LEDefinition2" )
    ref( "LEDefinition" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"gamma (s n) 0", gammaBc3 )

  val esGammaSc =
    Sequent(
      Seq( "Ant_0" -> hof"PAND(s(m),s(n))" ),
      Seq( "Suc_0" -> hof"CutDistinct(s(m),s(n))" ) )
  val gammaSc = Lemma( esGammaSc ) {
    unfold( "CutDistinct" ) atMost 1 in "Suc_0"
    unfold( "PAND" ) atMost 1 in "Ant_0"
    andL
    andR
    ref( "gamma" )
    orR
    allR( "Suc_0_1", fov"a" )
    exR( fov"a" )
    unfold( "POR" ) atMost 1 in "Ant_0_0"
    allL( fov"a" )
    orL
    allL( le"(suc a)" )
    orL
    andR
    trivial
    trivial
    allL( le"(suc a)" )
    orL
    andR
    trivial
    trivial
    ref( "LEDefinition2" )
    ref( "LEDefinition" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"gamma (s n) (s m)", gammaSc )

  val esPhiBc =
    Sequent(
      Seq(
        "Ant_0" -> hof"CutDistinct(0,0)",
        "Ant_1" -> hof"!x TopFuncDef(0,s(0),x)" ),
      Seq( "Suc_0" -> hof"?x (E(f(s(0),x), f(s(0),suc(x))) )" ) )
  val phiBc = Lemma( esPhiBc ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_0"
    orL
    exL( fov"a" )
    andL
    exR( fov"a" )
    allL( fov"a" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_0"
    cut( "cut1", hof"E(0, f(s(0), a))" )
    ref( "TransitivityE" )
    allL( le"(suc a)" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
    cut( "cut1", hof"E(0, f(s(0), suc(a)))" )
    ref( "TransitivityE" )
    ref( "NumericTransitivity" )
    allL( "Ant_0", foc"z" )
    ref( "minimalElement" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi 0 0", phiBc )

  val esPhiBc2 =
    Sequent(
      Seq(
        "Ant_0" -> hof"CutDistinct(0,s(n))",
        "Ant_1" -> hof"!x TopFuncDef(0,s(0),x)" ),
      Seq( "Suc_0" -> hof"?x (E(f(s(0),x), f(s(0),suc(x))) )" ) )
  val phiBc2 = Lemma( esPhiBc2 ) {
    cut( "cut", hof"CutDistinct(0,n)" )
    unfold( "CutDistinct" ) atMost 1 in "Ant_0"
    unfold( "CutDistinct" ) atMost 1 in "cut"
    orR
    focus( 1 )
    ref( "phi" )
    allR( "cut_1", fov"a" )
    exR( "cut_0", fov"a" )
    orL
    focus( 1 )
    andR
    allL( "Ant_0", fov"a" )
    ref( "ordcon" )
    allL( "Ant_0", le"(suc a)" )
    ref( "ordcon2" )
    exL( "Ant_0", fov"b" )
    exR( "Suc_0", fov"b" )
    andL
    allL( fov"b" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_0"
    cut( "cut1", hof"E(s(n), f(s(0), b))" )
    ref( "TransitivityE" )
    allL( le"(suc b)" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
    cut( "cut1", hof"E(s(n), f(s(0), suc(b)))" )
    ref( "TransitivityE" )
    ref( "NumericTransitivity" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi (s n) 0", phiBc2 )

  val esPhiBc3 =
    Sequent(
      Seq(
        "Ant_0" -> hof"CutDistinct(s(m),0)",
        "Ant_1" -> hof"!x TopFuncDef(s(m),s(s(m)),x)" ),
      Seq( "Suc_0" -> hof"?x (E(f(s(s(m)),x), f(s(s(m)),suc(x))) )" ) )
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
    cut( "cut2", hof"E(0, f((s (s m)),a))" )
    ref( "TransitivityE" )
    cut( "cut1", hof"E(0, f((s (s m)),(suc a)))" )
    ref( "TransitivityE" )
    exR( fov"a" )
    ref( "NumericTransitivity" )
    cut( "cut2", hof"E(0, f((s (s m)),a))" )
    ref( "TransitivityE" )
    exR( fov"a" )
    ref( "epsilon2" )
    allL( le"(suc a)" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
    orL
    cut( "cut1", hof"E(0, f((s (s m)),(suc a)))" )
    ref( "TransitivityE" )
    exR( fov"a" )
    ref( "epsilon" )
    exR( fov"a" )
    ref( "epsilon3" )
    allL( "Ant_0_1", hoc"z" )
    ref( "minimalElement" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi 0 (s m)", phiBc3 )

  val esPhiSc =
    Sequent(
      Seq(
        "Ant_0" -> hof"CutDistinct(s(m),s(n))",
        "Ant_1" -> hof"!x TopFuncDef(s(m),s(s(m)),x)" ),
      Seq( "Suc_0" -> hof"?x (E(f(s(s(m)),x), f(s(s(m)),suc(x))) )" ) )
  val phiSc = Lemma( esPhiSc ) {
    cut( "cut", hof"CutDistinct(s(m),n)" )
    ref( "mu" )
    ref( "phi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi (s n) (s m)", phiSc )

  val esMuBc =
    Sequent(
      Seq(
        "Ant_0" -> hof"CutDistinct(0,s(n))",
        "Ant_1" -> hof"!x TopFuncDef(0,k,x)" ),
      Seq(
        "Suc_0" -> hof"?x (E(f(k,x), f(k,suc(x))) )",
        "Suc_1" -> hof"CutDistinct(0,n)" ) )
  val muBc = Lemma( esMuBc ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_0"
    unfold( "CutDistinct" ) atMost 1 in "Suc_1"
    orR
    allR( fov"a" )
    orL
    focus( 1 )
    exR( "Suc_1_0", fov"a" )
    andR
    allL( "Ant_0", fov"a" )
    ref( "ordcon" )
    allL( "Ant_0", le"(suc a)" )
    ref( "ordcon2" )
    exL( fov"b" )
    andL
    allL( fov"b" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_0"
    cut( "cut2", hof"E(s(n), f(k,b))" )
    ref( "TransitivityE" )
    allL( le"(suc b)" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
    cut( "cut1", hof"E(s(n), f(k,(suc b)))" )
    ref( "TransitivityE" )
    exR( "Suc_0", fov"b" )
    ref( "NumericTransitivity" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"mu n 0 k", muBc )

  val esMuSc =
    Sequent(
      Seq(
        "Ant_0" -> hof"CutDistinct(s(m),s(n))",
        "Ant_1" -> hof"!x TopFuncDef(s(m),k,x)" ),
      Seq(
        "Suc_0" -> hof"?x (E(f(k,x), f(k,suc(x))) )",
        "Suc_1" -> hof"CutDistinct(s(m),n)" ) )
  val muSc = Lemma( esMuSc ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_0"
    unfold( "CutDistinct" ) atMost 1 in "Suc_1"
    andL
    andR
    focus( 1 )
    orR
    allR( fov"a" )
    orL
    focus( 1 )
    exR( "Suc_1_0", fov"a" )
    andR
    allL( "Ant_0_1", fov"a" )
    ref( "ordcon" )
    allL( "Ant_0_1", le"(suc a)" )
    ref( "ordcon2" )
    exL( fov"b" )
    andL
    allL( fov"b" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_0"
    orL
    cut( "cut2", hof"E(s(n), f(k,b))" )
    ref( "TransitivityE" )
    allL( le"(suc b)" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
    orL
    cut( "cut1", hof"E(s(n), f(k,(suc b)))" )
    ref( "TransitivityE" )
    exR( "Suc_0", fov"b" )
    ref( "NumericTransitivity" )
    exR( "Suc_0", fov"b" )
    exR( "Suc_1_0", fov"a" )
    ref( "theta" )
    allL( le"(suc b)" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
    orL
    cut( "cut1", hof"E(s(n), f(k,(suc b)))" )
    ref( "TransitivityE" )
    exR( "Suc_0", fov"b" )
    exR( "Suc_1_0", fov"a" )
    ref( "theta2" )
    exR( "Suc_0", fov"b" )
    exR( "Suc_1_0", fov"a" )
    ref( "theta3" )
    orL
    exL( fov"a" )
    andL
    allL( "Ant_1", fov"a" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_0"
    orL
    cut( "cut2", hof"E(s(n), f(k,a))" )
    ref( "TransitivityE" )
    allL( "Ant_1", le"(suc a)" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
    orL
    cut( "cut1", hof"E(s(n), f(k,suc(a)))" )
    ref( "TransitivityE" )
    exR( "Suc_0", fov"a" )
    ref( "NumericTransitivity" )
    exR( "Suc_0", fov"a" )
    ref( "epsilon4" )
    allL( "Ant_1", le"(suc a)" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
    orL
    cut( "cut1", hof"E(s(n), f(k,suc(a)))" )
    ref( "TransitivityE" )
    exR( "Suc_0", fov"a" )
    ref( "epsilon5" )
    exR( "Suc_0", fov"a" )
    ref( "epsilon6" )
    ref( "pi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"mu n (s m) k", muSc )

  /*

                           ********
                          **********
                         ***
                        ***
                       ***
                      **************
                      **************
                       ***
                        ***
                         ***
                          **********
                           ********
   */
  val esEpsilonBc =
    Sequent(
      Seq(
        "Ant_0" -> hof"E(0, f(k, suc(x)))",
        "Ant_1" -> hof"TopFuncDef(0, k, x)",
        "Ant_3" -> hof"CutDistinct(0,0)" ),
      Seq( "Suc_2" -> hof"E(f(k, x), f(k, suc(x)))" ) )
  val EpsilonBc = Lemma( esEpsilonBc ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_3"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1"
    orL
    exL( fov"b" )
    andL
    cut( "cut1", hof"E(0, f(k,x))" )
    ref( "StrongTransitivityE" )
    ref( "NumericTransitivity" )
    allL( "Ant_3", fov"x" )
    ref( "minimalElement" )

  }
  ctx += Context.ProofDefinitionDeclaration( le"epsilon 0 k x", EpsilonBc )

  val esEpsilonSc =
    Sequent(
      Seq(
        "Ant_0" -> hof"E(0, f(k, suc(x)))",
        "Ant_1" -> hof"TopFuncDef(s(m), k, x)",
        "Ant_3" -> hof"CutDistinct(s(m),0)" ),
      Seq( "Suc_2" -> hof"E(f(k, x), f(k, suc(x)))" ) )
  val EpsilonSc = Lemma( esEpsilonSc ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_3"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1"
    andL
    orL( "Ant_1" )
    orL( "Ant_3_1" )
    exL( fov"b" )
    andL
    cut( "cut1", hof"E(0, f(k, x))" )
    ref( "StrongTransitivityE" )
    ref( "NumericTransitivity" )
    allL( fov"x" )
    ref( "minimalElement" )
    ref( "epsilon" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"epsilon (s m) k x", EpsilonSc )

  val esEpsilon2Bc =
    Sequent(
      Seq(
        "Ant_0" -> hof"E(0, f(k, x))",
        "Ant_1" -> hof"TopFuncDef(0, k, suc(x))",
        "Ant_3" -> hof"CutDistinct(0,0)" ),
      Seq( "Suc_2" -> hof"E(f(k, x), f(k, suc(x)))" ) )
  val Epsilon2Bc = Lemma( esEpsilon2Bc ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_3"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1"
    orL
    exL( fov"b" )
    andL
    cut( "cut1", hof"E(0, f(k,suc(x)))" )
    ref( "StrongTransitivityE" )
    ref( "NumericTransitivity" )
    allL( fov"x" )
    ref( "minimalElement" )

  }
  ctx += Context.ProofDefinitionDeclaration( le"epsilon2 0 k x", Epsilon2Bc )

  val esEpsilon2Sc =
    Sequent(
      Seq(
        "Ant_0" -> hof"E(0, f(k, x))",
        "Ant_1" -> hof"TopFuncDef(s(m), k, suc(x))",
        "Ant_3" -> hof"CutDistinct(s(m),0)" ),
      Seq( "Suc_2" -> hof"E(f(k, x), f(k, suc(x)))" ) )
  val Epsilon2Sc = Lemma( esEpsilon2Sc ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_3"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1"
    andL
    orL( "Ant_1" )
    orL( "Ant_3_1" )
    exL( fov"b" )
    andL
    cut( "cut1", hof"E(0, f(k, (suc x)))" )
    ref( "StrongTransitivityE" )
    ref( "NumericTransitivity" )
    allL( fov"x" )
    ref( "minimalElement" )
    ref( "epsilon2" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"epsilon2 (s m) k x", Epsilon2Sc )

  val esEpsilon3Bc =
    Sequent(
      Seq(
        "Ant_0" -> hof"TopFuncDef(0, k, x)",
        "Ant_1" -> hof"TopFuncDef(0, k, suc(x))",
        "Ant_3" -> hof"CutDistinct(0,0)" ),
      Seq( "Suc_2" -> hof"E(f(k, x), f(k, suc(x)))" ) )
  val Epsilon3Bc = Lemma( esEpsilon3Bc ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_3"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_0"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1"
    orL
    exL( fov"b" )
    andL
    cut( "cut1", hof"E(0, f(k,suc(x)))" )
    ref( "StrongTransitivityE" )
    cut( "cut1", hof"E(0, f(k,x))" )
    ref( "StrongTransitivityE" )
    ref( "NumericTransitivity" )
    allL( fov"x" )
    ref( "minimalElement" )

  }
  ctx += Context.ProofDefinitionDeclaration( le"epsilon3 0 k x", Epsilon3Bc )

  val esEpsilon3Sc =
    Sequent(
      Seq(
        "Ant_0" -> hof"TopFuncDef(s(m), k, x)",
        "Ant_1" -> hof"TopFuncDef(s(m), k, suc(x))",
        "Ant_3" -> hof"CutDistinct(s(m),0)" ),
      Seq( "Suc_2" -> hof"E(f(k, x), f(k, suc(x)))" ) )
  val Epsilon3Sc = Lemma( esEpsilon3Sc ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_3"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_0"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1"
    andL
    orL( "Ant_3_1" )
    exL( fov"b" )
    andL
    orL( "Ant_0" )
    orL( "Ant_1" )
    cut( "cut1", hof"E(0, f(k, (suc x)))" )
    ref( "StrongTransitivityE" )
    cut( "cut2", hof"E(0, f(k, x))" )
    ref( "StrongTransitivityE" )
    ref( "NumericTransitivity" )
    cut( "cut2", hof"E(0, f(k, x))" )
    ref( "StrongTransitivityE" )
    ref( "epsilon2" )
    orL( "Ant_1" )
    cut( "cut1", hof"E(0, f(k, (suc x)))" )
    ref( "StrongTransitivityE" )
    ref( "epsilon" )
    ref( "epsilon3" )
    allL( fov"x" )
    ref( "minimalElement" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"epsilon3 (s m) k x", Epsilon3Sc )

  val esEpsilon4Bc =
    Sequent(
      Seq(
        "Ant_0" -> hof"E(s(n), f(k, x))",
        "Ant_1" -> hof"TopFuncDef(0, k, suc(x))",
        "Ant_3" -> hof"CutDistinct(0,s(n))" ),
      Seq(
        "Suc_1" -> hof"CutDistinct(0,n)",
        "Suc_2" -> hof"E(f(k, x), f(k, suc(x)))" ) )
  val Epsilon4Bc = Lemma( esEpsilon4Bc ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_3"
    unfold( "CutDistinct" ) atMost 1 in "Suc_1"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1"
    orR
    orL
    exL( fov"b" )
    andL
    cut( "cut1", hof"E(s(n), f(k, (suc x)))" )
    ref( "StrongTransitivityE" )
    ref( "NumericTransitivity" )
    allR( "Suc_1_1", fov"a" )
    exR( fov"a" )
    allL( fov"a" )
    andR
    ref( "ordcon" )
    allL( le"(suc a)" )
    ref( "ordcon2" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"epsilon4 0 k n x", Epsilon4Bc )

  val esEpsilon4Sc =
    Sequent(
      Seq(
        "Ant_0" -> hof"E(s(n), f(k, x))",
        "Ant_1" -> hof"TopFuncDef(s(m), k, suc(x))",
        "Ant_3" -> hof"CutDistinct(s(m),s(n))" ),
      Seq(
        "Suc_1" -> hof"CutDistinct(s(m),n)",
        "Suc_2" -> hof"E(f(k, x), f(k, suc(x)))" ) )
  val Epsilon4Sc = Lemma( esEpsilon4Sc ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_3"
    unfold( "CutDistinct" ) atMost 1 in "Suc_1"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1"
    andR
    andL
    orL( "Ant_3_1" )
    orL
    exL( fov"b" )
    andL
    cut( "cut1", hof"E(s(n), f(k, (suc x)))" )
    ref( "StrongTransitivityE" )
    ref( "NumericTransitivity" )
    ref( "epsilon4" )
    orL
    ref( "pi" )
    ref( "pi" )
    orR
    andL
    orL( "Ant_3_1" )
    orL
    exL( fov"c" )
    andL
    cut( "cut1", hof"E(s(n), f(k, (suc x)))" )
    ref( "StrongTransitivityE" )
    ref( "NumericTransitivity" )
    allR( "Suc_1_1", fov"e" )
    exR( fov"e" )
    ref( "theta" )
    allR( "Suc_1_1", fov"b" )
    exR( fov"b" )
    allL( fov"b" )
    andR
    ref( "ordcon" )
    allL( le"(suc b)" )
    ref( "ordcon2" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"epsilon4 (s m) k n x", Epsilon4Sc )

  val esEpsilon5Bc =
    Sequent(
      Seq(
        "Ant_0" -> hof"E(s(n), f(k, suc(x)))",
        "Ant_1" -> hof"TopFuncDef(0, k, x)",
        "Ant_3" -> hof"CutDistinct(0,s(n))" ),
      Seq(
        "Suc_1" -> hof"CutDistinct(0,n)",
        "Suc_2" -> hof"E(f(k, x), f(k, suc(x)))" ) )
  val Epsilon5Bc = Lemma( esEpsilon5Bc ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_3"
    unfold( "CutDistinct" ) atMost 1 in "Suc_1"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1"
    orR
    orL
    exL( fov"b" )
    andL
    cut( "cut1", hof"E(s(n), f(k, x))" )
    ref( "StrongTransitivityE" )
    ref( "NumericTransitivity" )
    allR( "Suc_1_1", fov"a" )
    exR( fov"a" )
    allL( fov"a" )
    andR
    ref( "ordcon" )
    allL( le"(suc a)" )
    ref( "ordcon2" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"epsilon5 0 k n x", Epsilon5Bc )

  val esEpsilon5Sc =
    Sequent(
      Seq(
        "Ant_0" -> hof"E(s(n), f(k, suc(x)))",
        "Ant_1" -> hof"TopFuncDef(s(m), k,x)",
        "Ant_3" -> hof"CutDistinct(s(m),s(n))" ),
      Seq(
        "Suc_1" -> hof"CutDistinct(s(m),n)",
        "Suc_2" -> hof"E(f(k, x), f(k, suc(x)))" ) )
  val Epsilon5Sc = Lemma( esEpsilon5Sc ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_3"
    unfold( "CutDistinct" ) atMost 1 in "Suc_1"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1"
    andR
    andL
    orL( "Ant_3_1" )
    orL
    exL( fov"b" )
    andL
    cut( "cut1", hof"E(s(n), f(k, x))" )
    ref( "StrongTransitivityE" )
    ref( "NumericTransitivity" )
    ref( "epsilon5" )
    orL
    ref( "pi" )
    ref( "pi" )
    orR
    andL
    orL( "Ant_3_1" )
    orL
    exL( fov"c" )
    andL
    cut( "cut1", hof"E(s(n), f(k, x))" )
    ref( "StrongTransitivityE" )
    ref( "NumericTransitivity" )
    allR( "Suc_1_1", fov"e" )
    exR( fov"e" )
    ref( "theta2" )
    allR( "Suc_1_1", fov"b" )
    exR( fov"b" )
    allL( fov"b" )
    andR
    ref( "ordcon" )
    allL( le"(suc b)" )
    ref( "ordcon2" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"epsilon5 (s m) k n x", Epsilon5Sc )

  val esEpsilon6Bc =
    Sequent(
      Seq(
        "Ant_0" -> hof"TopFuncDef(0, k, x)",
        "Ant_1" -> hof"TopFuncDef(0, k, suc(x))",
        "Ant_3" -> hof"CutDistinct(0,s(n))" ),
      Seq(
        "Suc_1" -> hof"CutDistinct(0,n)",
        "Suc_2" -> hof"E(f(k, x), f(k, suc(x)))" ) )
  val Epsilon6Bc = Lemma( esEpsilon6Bc ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_3"
    unfold( "CutDistinct" ) atMost 1 in "Suc_1"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_0"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1"

    orR
    orL
    exL( fov"b" )
    andL
    cut( "cut1", hof"E(s(n), f(k, x))" )
    ref( "StrongTransitivityE" )
    cut( "cut1", hof"E(s(n), f(k, suc(x)))" )
    ref( "StrongTransitivityE" )
    ref( "NumericTransitivity" )
    allR( "Suc_1_1", fov"a" )
    exR( fov"a" )
    allL( fov"a" )
    andR
    ref( "ordcon" )
    allL( le"(suc a)" )
    ref( "ordcon2" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"epsilon6 0 k n x", Epsilon6Bc )

  val esEpsilon6Sc =
    Sequent(
      Seq(
        "Ant_0" -> hof"TopFuncDef(s(m), k,x)",
        "Ant_1" -> hof"TopFuncDef(s(m), k,suc(x))",
        "Ant_3" -> hof"CutDistinct(s(m),s(n))" ),
      Seq(
        "Suc_1" -> hof"CutDistinct(s(m),n)",
        "Suc_2" -> hof"E(f(k, x), f(k, suc(x)))" ) )
  val Epsilon6Sc = Lemma( esEpsilon6Sc ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_3"
    unfold( "CutDistinct" ) atMost 1 in "Suc_1"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_0"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1"
    andR
    andL
    orL( "Ant_3_1" )
    orL( "Ant_0" )
    exL( fov"b" )
    andL
    cut( "cut1", hof"E(s(n), f(k, x))" )
    ref( "StrongTransitivityE" )
    orL( "Ant_1" )
    cut( "cut1", hof"E(s(n), f(k, suc(x)))" )
    ref( "StrongTransitivityE" )
    ref( "NumericTransitivity" )
    ref( "epsilon4" )
    orL
    exL( fov"c" )
    andL
    cut( "cut1", hof"E(s(n), f(k, suc(x)))" )
    ref( "StrongTransitivityE" )
    ref( "epsilon5" )
    ref( "epsilon6" )
    ref( "pi" )
    andL
    orR
    orL( "Ant_3_1" )
    exL( fov"e" )
    orL( "Ant_0" )
    andL
    cut( "cut1", hof"E(s(n), f(k, x))" )
    ref( "StrongTransitivityE" )
    orL
    cut( "cut2", hof"E(s(n), f(k, suc(x)))" )
    ref( "StrongTransitivityE" )
    ref( "NumericTransitivity" )
    allR( fov"r" )
    exR( fov"r" )
    ref( "theta" )
    andL
    orL
    cut( "cut2", hof"E(s(n), f(k, suc(x)))" )
    ref( "StrongTransitivityE" )
    allR( fov"r" )
    exR( fov"r" )
    ref( "theta2" )
    allR( fov"r" )
    exR( fov"r" )
    ref( "theta3" )
    allR( fov"r" )
    exR( fov"r" )
    allL( fov"r" )
    andR
    ref( "ordcon" )
    allL( le"(suc r)" )
    ref( "ordcon2" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"epsilon6 (s m) k n x", Epsilon6Sc )

  val esThetaBC =
    Sequent(
      Seq(
        "Ant_0" -> hof"E(s(n), f(k, y))",
        "Ant_1" -> hof"TopFuncDef(0, k, suc(y))",
        "Ant_3" -> hof"CutDistinct(0,s(n))" ),
      Seq(
        "Suc_0" -> hof"E(n, f(w, x)) & E(n, f(w, suc(x)))",
        "Suc_1" -> hof"LE(f(w, x), n)",
        "Suc_2" -> hof"E(f(k, y), f(k, suc(y)))" ) )
  val ThetaBC = Lemma( esThetaBC ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_3"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1"
    orL
    exL( fov"b" )
    andL
    cut( "cut1", hof"E(s(n), f(k, suc(y)))" )
    ref( "StrongTransitivityE" )
    ref( "NumericTransitivity" )
    andR
    allL( fov"x" )
    ref( "ordcon" )
    allL( le"(suc x)" )
    ref( "ordcon2" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"theta 0 k w n x y", ThetaBC )

  val esThetaSC =
    Sequent(
      Seq(
        "Ant_0" -> hof"E(s(n), f(k, y))",
        "Ant_1" -> hof"TopFuncDef(s(m), k, suc(y))",
        "Ant_3" -> hof"CutDistinct(s(m),s(n))" ),
      Seq(
        "Suc_0" -> hof"E(n, f(w, x)) & E(n, f(w, suc(x)))",
        "Suc_1" -> hof"LE(f(w, x), n)",
        "Suc_2" -> hof"E(f(k, y), f(k, suc(y)))" ) )
  val ThetaSC = Lemma( esThetaSC ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_3"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1"
    andL
    orL( "Ant_3_1" )
    exL( fov"b" )
    andL
    orL
    cut( "cut1", hof"E(s(n), f(k, suc(y)))" )
    ref( "StrongTransitivityE" )
    ref( "NumericTransitivity" )
    ref( "theta" )
    andR
    allL( fov"x" )
    ref( "ordcon" )
    allL( le"(suc x)" )
    ref( "ordcon2" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"theta (s m) k w n x y", ThetaSC )

  val esTheta2BC =
    Sequent(
      Seq(
        "Ant_0" -> hof"E(s(n), f(k, suc(y)))",
        "Ant_1" -> hof"TopFuncDef(0, k, y)",
        "Ant_3" -> hof"CutDistinct(0,s(n))" ),
      Seq(
        "Suc_0" -> hof"E(n, f(w, x)) & E(n, f(w, suc(x)))",
        "Suc_1" -> hof"LE(f(w, x), n)",
        "Suc_2" -> hof"E(f(k, y), f(k, suc(y)))" ) )
  val Theta2BC = Lemma( esTheta2BC ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_3"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1"
    orL
    exL( fov"b" )
    andL
    cut( "cut1", hof"E(s(n), f(k, y))" )
    ref( "StrongTransitivityE" )
    ref( "NumericTransitivity" )
    andR
    allL( fov"x" )
    ref( "ordcon" )
    allL( le"(suc x)" )
    ref( "ordcon2" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"theta2 0 k w n x y", Theta2BC )

  val esTheta2SC =
    Sequent(
      Seq(
        "Ant_0" -> hof"E(s(n), f(k, suc(y)))",
        "Ant_1" -> hof"TopFuncDef(s(m), k, y)",
        "Ant_3" -> hof"CutDistinct(s(m),s(n))" ),
      Seq(
        "Suc_0" -> hof"E(n, f(w, x)) & E(n, f(w, suc(x)))",
        "Suc_1" -> hof"LE(f(w, x), n)",
        "Suc_2" -> hof"E(f(k, y), f(k, suc(y)))" ) )
  val Theta2SC = Lemma( esTheta2SC ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_3"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1"
    andL
    orL( "Ant_3_1" )
    exL( fov"b" )
    andL
    orL
    cut( "cut1", hof"E(s(n), f(k, y))" )
    ref( "StrongTransitivityE" )
    ref( "NumericTransitivity" )
    ref( "theta2" )
    andR
    allL( fov"x" )
    ref( "ordcon" )
    allL( le"(suc x)" )
    ref( "ordcon2" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"theta2 (s m) k w n x y", Theta2SC )

  val esTheta3BC =
    Sequent(
      Seq(
        "Ant_0" -> hof"TopFuncDef(0, k, suc(y))",
        "Ant_1" -> hof"TopFuncDef(0, k, y)",
        "Ant_3" -> hof"CutDistinct(0,s(n))" ),
      Seq(
        "Suc_0" -> hof"E(n, f(w, x)) & E(n, f(w, suc(x)))",
        "Suc_1" -> hof"LE(f(w, x), n)",
        "Suc_2" -> hof"E(f(k, y), f(k, suc(y)))" ) )
  val Theta3BC = Lemma( esTheta3BC ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_3"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_0"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1"
    orL
    exL( fov"b" )
    andL
    cut( "cut1", hof"E(s(n), f(k, y))" )
    ref( "StrongTransitivityE" )
    cut( "cut1", hof"E(s(n), f(k, suc(y)))" )
    ref( "StrongTransitivityE" )
    ref( "NumericTransitivity" )
    andR
    allL( fov"x" )
    ref( "ordcon" )
    allL( le"(suc x)" )
    ref( "ordcon2" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"theta3 0 k w n x y", Theta3BC )

  val esTheta3SC =
    Sequent(
      Seq(
        "Ant_0" -> hof"TopFuncDef(s(m), k, suc(y))",
        "Ant_1" -> hof"TopFuncDef(s(m), k, y)",
        "Ant_3" -> hof"CutDistinct(s(m),s(n))" ),
      Seq(
        "Suc_0" -> hof"E(n, f(w, x)) & E(n, f(w, suc(x)))",
        "Suc_1" -> hof"LE(f(w, x), n)",
        "Suc_2" -> hof"E(f(k, y), f(k, suc(y)))" ) )
  val Theta3SC = Lemma( esTheta3SC ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_3"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_0"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1"
    andL
    orL( "Ant_3_1" )
    exL( fov"b" )
    andL
    orL( "Ant_1" )
    cut( "cut1", hof"E(s(n), f(k, y))" )
    ref( "StrongTransitivityE" )
    orL( "Ant_0" )
    cut( "cut1", hof"E(s(n), f(k, suc(y)))" )
    ref( "StrongTransitivityE" )
    ref( "NumericTransitivity" )
    ref( "theta" )
    orL
    cut( "cut1", hof"E(s(n), f(k, suc(y)))" )
    ref( "StrongTransitivityE" )
    ref( "theta2" )
    ref( "theta3" )
    andR
    allL( fov"x" )
    ref( "ordcon" )
    allL( le"(suc x)" )
    ref( "ordcon2" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"theta3 (s m) k w n x y", Theta3SC )

  val esPiBC =
    Sequent(
      Seq( "Ant_0" -> hof"!x LE(f(k, x), s(n))" ),
      Seq( "Suc_0" -> hof"CutDistinct(0,n)" ) )
  val PiBC = Lemma( esPiBC ) {
    unfold( "CutDistinct" ) atMost 1 in "Suc_0"
    orR
    allR( fov"a" )
    exR( fov"a" )
    andR
    allL( fov"a" )
    ref( "ordcon" )
    allL( le"(suc a)" )
    ref( "ordcon2" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"pi n 0 k ", PiBC )

  val esPiSC =
    Sequent(
      Seq( "Ant_0" -> hof"!x LE(f(k, x), s(n))" ),
      Seq( "Suc_0" -> hof"CutDistinct(s(m),n)" ) )
  val PiSC = Lemma( esPiSC ) {
    unfold( "CutDistinct" ) atMost 1 in "Suc_0"
    andR
    ref( "pi" )
    orR
    allR( fov"a" )
    exR( fov"a" )
    andR
    allL( fov"a" )
    ref( "ordcon" )
    allL( le"(suc a)" )
    ref( "ordcon2" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"pi n (s m) k  ", PiSC )

}

