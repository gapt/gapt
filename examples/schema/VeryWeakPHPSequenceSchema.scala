package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.PrimRecFun
import at.logic.gapt.proofs.{ Context, Sequent }
import at.logic.gapt.proofs.gaptic.TacticsProof
import at.logic.gapt.proofs.gaptic._

object VeryWeakPHPSequenceSchema extends TacticsProof {
  ctx += Context.InductiveType( "nat", hoc"0 : nat", hoc"s : nat>nat" )
  ctx += Context.Sort( "i" )
  ctx += hoc"f:nat>i>nat"
  ctx += hoc"suc:i>i"
  ctx += hoc"z:i"
  ctx += hoc"E: nat>nat>o"
  ctx += hoc"LE: nat>nat>o"
 //Needs to be reworked into exists x cutdistinct(m,n,x)
 //otherwise we run into eigenvariable problems :/
  ctx += hoc"omega: nat>nat>nat"
  ctx += hoc"gamma: nat>nat>i>nat"
  ctx += hoc"phi: nat>nat>nat"
  ctx += hoc"mu: nat>nat>nat>nat"
  ctx += hoc"epsilon: nat>nat>nat>nat>nat"// prove
  ctx += hoc"epsilon2: nat>nat>nat>nat>i>nat"// prove
  ctx += hoc"epsilon3: nat>nat>nat>i>nat"// prove
  ctx += hoc"epsilon4: nat>nat>nat>i>nat"// prove
  ctx += hoc"epsilon5: nat>nat>nat>i>nat"// prove
  ctx += hoc"theta: nat>nat>nat>i>nat" // prove
  ctx += hoc"zeta: nat>nat>nat>i>nat"// prove
  ctx += hoc"pi: nat>nat>nat>nat" // prove

  ctx += PrimRecFun( hoc"POR:nat>nat>i>o", "POR 0 m x = E 0 (f m x) ", "POR (s y) m x = (E (s y) (f m x) ∨ POR y m x)" )
  ctx += PrimRecFun( hoc"PAND:nat>nat>o", "(PAND 0 n)= (∀x (POR n 0 x))", "(PAND (s m) n) = ((∀x (POR n (s m) x)) & (PAND m n))" )
  ctx += PrimRecFun( hoc"TopFuncDef:nat>nat>i>o", "(TopFuncDef 0 k x)= (E (f 0 x) (f k x)) ", "(TopFuncDef (s m) k x)= ((E (f (s m) x) (f k x)) | (TopFuncDef m k x))" )
  ctx += PrimRecFun(
    hoc"CutDistinct:nat>nat>i>o",
    "(CutDistinct 0 n x) =  (  ((E n (f 0 x)) & (E n (f 0 (suc x))) ) | (∀y (LE (f 0 y) n)))",
    "(CutDistinct (s m) n x) = (" +
      "(CutDistinct m n x) & (  ((E n (f (s m) x)) & (E n (f (s m) (suc x))) ) | (∀y (LE (f (s m) y) n)))" +
      ")" )
  ctx += "LEDefinition" -> hos"POR(n,m,a) :- LE(f(m,a), s(n))"
  ctx += "LEDefinition2" -> hos"POR(n,m, suc(a)) :- LE(f(m,a), s(n))"
  ctx += "NumericTransitivity" -> hos"E(n,f(m,a)),E(n,f(m,suc(a))) :- E(f(m,a), f(m,suc(a)))"
  ctx += "TransitivityE" -> hos"E(a,b),E(b,c) :- E(a,c)"
  ctx += "minimalElement" -> hos"LE(f(m,z),0) :- "
  ctx += "ordcon" -> hos"LE(f(m,a),s(n)) :- E(n,f(m,a)), LE(f(m,a),n)"
  ctx += "ordcon2" -> hos"LE(f(m,suc(a)),s(n)) :- E(n,f(m,suc(a))), LE(f(m,a),n)"

  val esOmega = Sequent(
    Seq(
      hof"PAND(m,n)",
      hof"!x TopFuncDef(m,s(m),x)" ),
    Seq( hof"?x ( E(f(s(m),x), f(s(m),suc(x))) )" ) )
  ctx += Context.ProofNameDeclaration( le"omega n m", esOmega )
  val esGamma = Sequent(
    Seq(hof"PAND(m,n)"),
    Seq(hof"CutDistinct(m,n,x)"))
  ctx += Context.ProofNameDeclaration( le"gamma n m x", esGamma )
  val esPhi = Sequent(
    Seq(
      hof"?x CutDistinct(m,n,x)",
      hof"!x TopFuncDef(m,s(m),x)" ),
    Seq( hof"?x ( E(f(s(m),x), f(s(m),suc(x))) )" ) )
  ctx += Context.ProofNameDeclaration( le"phi n m", esPhi )
  val esMu = Sequent(
    Seq(
      hof"?x CutDistinct(m,s(n),x)",
      hof"!x TopFuncDef(m,k,x)" ),
    Seq( hof"?x ( E(f(k,x), f(k,suc(x))) )",
         hof"?x CutDistinct(m,n,x)") )
  ctx += Context.ProofNameDeclaration( le"mu n m k", esMu )
  val esEpsilon = Sequent(
    Seq( hof"!x TopFuncDef(m, w,x)",
        hof"?x CutDistinct(k,n, x)"),
    Seq( hof"?x E(f(w, x), f(w, suc(x)))" ) )
  ctx += Context.ProofNameDeclaration( le"epsilon m k w n", esEpsilon )
  val esEpsilon2 = Sequent(
    Seq( hof"!x TopFuncDef(m,w,x)",
      hof"?x CutDistinct(k,s(n),x)"),
    Seq( hof"?x E(f(w, x), f(w, suc(x)))",
         hof"(E(n, f(m, y)) & E(n, f(m, suc(y))))",
         hof"LE(f(m, y), n)") )
  ctx += Context.ProofNameDeclaration( le"epsilon2 m k w n y", esEpsilon2 )
  val esEpsilon3 = Sequent(
    Seq( hof"TopFuncDef(m, k,suc(x))",
         hof"E(s(n), f(k, x))",
         hof"?x CutDistinct(m,s(n),x)"),
    Seq( hof"?x E(f(k, x), f(k, suc(x)))",
         hof"?x CutDistinct(m,n,x)" ) )
  ctx += Context.ProofNameDeclaration( le"epsilon3 m k n x", esEpsilon3 )
  val esEpsilon4 = Sequent(
    Seq( hof"TopFuncDef(m, k,x)",
      hof"E(s(n), f(k, suc(x)))",
      hof"?x CutDistinct(m,s(n),x)"),
    Seq( hof"?x E(f(k, x), f(k, suc(x)))",
      hof"?x  CutDistinct(m,n,x)" ) )
  ctx += Context.ProofNameDeclaration( le"epsilon4 m k n x", esEpsilon4 )

  val esEpsilon5 = Sequent(
    Seq( hof"TopFuncDef(m, k,x)",
         hof"TopFuncDef(m, k,suc(x))",
         hof"?x CutDistinct(m,s(n),x)"),
    Seq( hof"?x E(f(k, x), f(k, suc(x)))",
      hof"?x CutDistinct(m,n,x)" ) )
  ctx += Context.ProofNameDeclaration( le"epsilon5 m k n x", esEpsilon5)

  val eszeta = Sequent(
    Seq(
      hof"?x CutDistinct(m,n,x)",
      hof"TopFuncDef(m, k, x)",
      hof"TopFuncDef(m, k, suc(x))" ),
    Seq( hof" E(f(k,x), f(k,suc(x))) " ) )
  ctx += Context.ProofNameDeclaration( le"zeta n m k x", eszeta )
  val espi = Sequent(
    Seq( hof"!x LE(f(k, x), s(n))" ),
    Seq( hof"?x CutDistinct(m,n,x)" ) )
  ctx += Context.ProofNameDeclaration( le"pi n m k", espi )
  //The base case of  omega
  val esOmegaBc =
    Sequent(
      Seq(
        "Ant_0" -> hof"PAND(0,0)",
        "Ant_1" -> hof"!x TopFuncDef(0,s(0),x)" ),
      Seq( "Suc_0" -> hof"?x (E(f(s(0),x), f(s(0),suc(x))))" ) )
  val omegaBc = Lemma( esOmegaBc ) {
    cut( "cut", hof"?x CutDistinct(0,0,x)" )
    unfold( "CutDistinct" ) atMost 1 in "cut"
    unfold( "PAND" ) atMost 1 in "Ant_0"
    exR("cut",hoc"z")
    orR
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
    cut( "cut", hof"?x CutDistinct(s(m),0,x)" )
    unfold( "CutDistinct" ) atMost 1 in "cut"
    unfold( "PAND" ) atMost 1 in "Ant_0"
    andL
    exR("cut",hoc"z")
    andR
    ref( "gamma" )
    orR
    allR(fov"a")
    exR("cut",fov"a")
    andR("cut_1")
    ref( "gamma" )
    orR
    allL("Ant_0_0",fov"a")
    unfold( "POR" ) atMost 1 in "Ant_0_0_0"
    allL("Ant_0_0",le"(suc a)")
    unfold( "POR" ) atMost 1 in "Ant_0_0_1"
    andR("cut_1_0")
       trivial
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
    cut( "cut", hof"?x CutDistinct(0,s(n),x)" )
    unfold( "CutDistinct" ) atMost 1 in "cut"
    unfold( "PAND" ) atMost 1 in "Ant_0"
    exR( "cut", hoc"z" )
    orR
    allR( "cut_0_1", fov"a" )
    exR( "cut", fov"a"  )
    orR

     andR("cut_1_0")
     allL( "Ant_0", fov"a" )
     unfold( "POR" ) atMost 1 in "Ant_0_0"
     orL
     trivial
     ref( "LEDefinition" )
     allL( "Ant_0", le"(suc a)" )
     unfold( "POR" ) atMost 1 in "Ant_0_0"
     orL
     trivial
     ref( "LEDefinition2" )
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
    cut( "cut", hof"?x CutDistinct(s(m),s(n),x)" )
    unfold( "CutDistinct" ) atMost 1 in "cut"
    unfold( "PAND" ) atMost 1 in "Ant_0"
    andL
    exR("cut",hoc"z")
    andR
    ref( "gamma" )
     orR
    allR(fov"a")
    exR("cut",fov"a")
    andR("cut_1")
    ref( "gamma" )
    orR
     allL("Ant_0_0",fov"a")
     unfold( "POR" ) atMost 1 in "Ant_0_0_0"
     allL("Ant_0_0",le"(suc a)")
     unfold( "POR" ) atMost 1 in "Ant_0_0_1"
     orL("Ant_0_0_0")
     orL("Ant_0_0_1")
     andR("cut_1_0")
     trivial
     trivial
     ref( "LEDefinition2" )
     ref( "LEDefinition" )
     ref( "phi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"omega (s n) (s m)", OmegaSc )

  val esGammaBc =
    Sequent(
      Seq("Ant_0" -> hof"PAND(0,0)"),
      Seq("Suc_0" -> hof" CutDistinct(0,0,x)") )
  val gammaBc = Lemma( esGammaBc ) {
    unfold( "CutDistinct" ) atMost 1 in "Suc_0"
    unfold( "PAND" ) atMost 1 in "Ant_0"
    orR
    allR( "Suc_0_1", fov"a")
    unfold( "POR" ) atMost 1 in "Ant_0"
    allL(fov"x")
    allL(le"(suc x)")
    andR
    trivial
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"gamma 0 0 x", gammaBc )
  val esGammaBc2 =
    Sequent(
      Seq("Ant_0" -> hof"PAND(s(m),0)"),
      Seq("Suc_0" -> hof"CutDistinct(s(m),0,x)") )
  val gammaBc2 = Lemma( esGammaBc2 ) {
    unfold( "CutDistinct" ) atMost 1 in "Suc_0"
    unfold( "PAND" ) atMost 1 in "Ant_0"
    andL
    andR
    ref( "gamma" )
    orR
    allR( "Suc_0_1", fov"a")
    unfold( "POR" ) atMost 1 in "Ant_0_0"
    allL(fov"x")
    allL(le"(suc x)")
    andR
    trivial
    trivial
  }
  ctx += Context.ProofDefinitionDeclaration( le"gamma 0 (s m) x", gammaBc2 )

  val esGammaBc3 =
    Sequent(
      Seq("Ant_0" -> hof"PAND(0,s(n))"),
      Seq("Suc_0" -> hof" CutDistinct(0,s(n),x)") )
  val gammaBc3 = Lemma( esGammaBc3 ) {
    unfold( "CutDistinct" ) atMost 1 in "Suc_0"
    unfold( "PAND" ) atMost 1 in "Ant_0"
    orR
    allR( "Suc_0_1", fov"a")
    unfold( "POR" ) atMost 1 in "Ant_0"
    allL(fov"x")
    orL
    allL(le"(suc x)")
    orL
    andR
    trivial
    trivial
    allL(le"(suc x)")
    orL
    andR
    trivial
    trivial
 //   ref( "LEDefinition2" ) //FUCK!!!!!
 //   ref( "LEDefinition" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"gamma (s n) 0", gammaBc3 )


  val esGammaSc  =
    Sequent(
      Seq("Ant_0" -> hof"PAND(s(m),s(n))"),
      Seq("Suc_0" -> hof"?x CutDistinct(s(m),s(n),x)") )
  val gammaSc = Lemma( esGammaSc ) {
    unfold( "CutDistinct" ) atMost 1 in "Suc_0"
    unfold( "PAND" ) atMost 1 in "Ant_0"
    andL
    andR
    ref( "gamma" )
    orR
    allR( "Suc_0_1", fov"a")
    exR(fov"a")
    unfold( "POR" ) atMost 1 in "Ant_0_0"
    allL(fov"a")
    orL
    allL(le"(suc a)")
    orL
    andR
    trivial
    trivial
    allL(le"(suc a)")
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
      Seq( "Ant_0" -> hof"?x CutDistinct(0,0,x)",
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
    allL("Ant_0", foc"z" )
    ref( "minimalElement" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi 0 0", phiBc )

  val esPhiBc2 =
    Sequent(
      Seq( "Ant_0" -> hof"?x CutDistinct(0,s(n),x)",
        "Ant_1" -> hof"!x TopFuncDef(0,s(0),x)" ),
      Seq( "Suc_0" -> hof"?x (E(f(s(0),x), f(s(0),suc(x))) )" ) )
  val phiBc2 = Lemma( esPhiBc2 ) {
    cut("cut",hof"?x CutDistinct(0,n,x)")
    unfold( "CutDistinct" ) atMost 1 in "Ant_0"
    unfold( "CutDistinct" ) atMost 1 in "cut"
    orR
    focus(1)
    ref( "phi" )
    allR("cut_1",fov"a")
    exR("cut_0",fov"a")
    orL
    focus(1)
    andR
    allL("Ant_0",fov"a")
    ref( "ordcon" )
    allL("Ant_0",le"(suc a)")
    ref( "ordcon2" )
    exL("Ant_0",fov"b")
    exR("Suc_0",fov"b")
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
  ctx += Context.ProofDefinitionDeclaration( le"phi (s n) 0", phiBc2)

  val esPhiBc3 =
    Sequent(
      Seq( "Ant_0" -> hof"?x CutDistinct(s(m),0,x)",
        "Ant_1" -> hof"!x TopFuncDef(s(m),s(s(m)),x)" ),
      Seq( "Suc_0" -> hof"?x (E(f(s(s(m)),x), f(s(s(m)),suc(x))) )" ) )
  val phiBc3 = Lemma( esPhiBc3 ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_0"
    andL
    orL
    exL(fov"a")
    andL
    allL(fov"a")
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_0"
    orL
    allL(le"(suc a)")
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
    orL
    cut( "cut2", hof"E(0, f((s (s m)),a))" )
    ref( "TransitivityE" )
    cut( "cut1", hof"E(0, f((s (s m)),(suc a)))" )
    ref( "TransitivityE" )
    exR(fov"a")
    ref( "NumericTransitivity" )
    cut( "cut2", hof"E(0, f((s (s m)),a))" )
    ref( "TransitivityE" )
    exR(fov"a")
    ref( "epsilon" )
    allL(le"(suc a)")
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
    orL
    cut( "cut1", hof"E(0, f((s (s m)),(suc a)))" )
    ref( "TransitivityE" )
    exR(fov"a")
    ref( "epsilon" )
    exR(fov"a")
    ref( "epsilon" )
     allL("Ant_0_1",hoc"z")
     ref( "minimalElement" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi 0 (s m)", phiBc3)


  val esPhiSc =
    Sequent(
      Seq( "Ant_0" -> hof"?x CutDistinct(s(m),s(n),x)",
        "Ant_1" -> hof"!x TopFuncDef(s(m),s(s(m)),x)" ),
      Seq( "Suc_0" -> hof"?x (E(f(s(s(m)),x), f(s(s(m)),suc(x))) )" ) )
  val phiSc = Lemma( esPhiSc ) {
    cut("cut",hof"?x CutDistinct(s(m),n,x)")
    ref( "mu" )
    ref( "phi")
  }
  ctx += Context.ProofDefinitionDeclaration( le"phi (s n) (s m)", phiSc)

  val esMuBc =
    Sequent(
      Seq( "Ant_0" -> hof"?x CutDistinct(0,s(n),x)",
        "Ant_1" -> hof"!x TopFuncDef(0,k,x)" ),
      Seq( "Suc_0" -> hof"?x (E(f(k,x), f(k,suc(x))) )",
        "Suc_1" -> hof"?x CutDistinct(0,n,x)") )
  val muBc = Lemma( esMuBc ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_0"
    unfold( "CutDistinct" ) atMost 1 in "Suc_1"
    orR
    allR(fov"a")
    orL
    focus(1)
    exR("Suc_1_0",fov"a")
    andR
    allL("Ant_0",fov"a")
    ref( "ordcon" )
    allL("Ant_0",le"(suc a)")
    ref( "ordcon2" )
    exL(fov"b")
    andL
    allL(fov"b")
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_0"
    cut( "cut2", hof"E(s(n), f(k,b))" )
    ref( "TransitivityE" )
    allL(le"(suc b)")
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
    cut( "cut1", hof"E(s(n), f(k,(suc b)))" )
    ref( "TransitivityE" )
    exR("Suc_0",fov"b")
    ref( "NumericTransitivity" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"mu n 0 k", muBc)

  val esMuSc =
    Sequent(
      Seq( "Ant_0" -> hof"?x CutDistinct(s(m),s(n),x)",
        "Ant_1" -> hof"!x TopFuncDef(s(m),k,x)" ),
      Seq( "Suc_0" -> hof"?x (E(f(k,x), f(k,suc(x))) )",
           "Suc_1" -> hof"?x CutDistinct(s(m),n,x)") )
  val muSc = Lemma( esMuSc ) {
      unfold( "CutDistinct" ) atMost 1 in "Ant_0"
      unfold( "CutDistinct" ) atMost 1 in "Suc_1"
      andL
      andR
      focus(1)
      orR
      allR(fov"a")
      orL
      focus(1)
      exR("Suc_1_0",fov"a")
      andR
      allL("Ant_0_1",fov"a")
      ref( "ordcon" )
      allL("Ant_0_1",le"(suc a)")
      ref( "ordcon2" )
      exL(fov"b")
      andL
      allL(fov"b")
      unfold( "TopFuncDef" ) atMost 1 in "Ant_1_0"
      orL
      cut( "cut2", hof"E(s(n), f(k,b))" )
      ref( "TransitivityE" )
      allL(le"(suc b)")
      unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
      orL
      cut( "cut1", hof"E(s(n), f(k,(suc b)))" )
      ref( "TransitivityE" )
      exR("Suc_0",fov"b")
      ref( "NumericTransitivity" )
      exR("Suc_0",fov"b")
      exR("Suc_1_0",fov"a")
      ref( "epsilon2" )
     allL(le"(suc b)")
     unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
     orL
     cut( "cut1", hof"E(s(n), f(k,(suc b)))" )
     ref( "TransitivityE" )
     exR("Suc_0",fov"b")
     exR("Suc_1_0",fov"a")
     ref( "epsilon2" )
     exR("Suc_0",fov"b")
     exR("Suc_1_0",fov"a")
     ref( "epsilon2" )
     orL
     exL(fov"a")
   andL
   allL("Ant_1",fov"a")
   unfold( "TopFuncDef" ) atMost 1 in "Ant_1_0"
   orL
   cut( "cut2", hof"E(s(n), f(k,a))" )
   ref( "TransitivityE" )
   allL("Ant_1",le"(suc a)")
   unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
   orL
   cut( "cut1", hof"E(s(n), f(k,suc(a)))" )
   ref( "TransitivityE" )
   exR("Suc_0",fov"a")
   ref( "NumericTransitivity" )
   cut( "cut2", hof"E(s(n), f(k,a))" )
   ref( "TransitivityE" )
   exR("Suc_0",fov"a")
      ref( "epsilon3" )
     allL("Ant_1",le"(suc a)")
      unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
      orL
      cut( "cut1", hof"E(s(n), f(k,suc(a)))" )
      ref( "TransitivityE" )
      exR("Suc_0",fov"a")
    ref( "epsilon4" )
      exR("Suc_0",fov"a")
     ref( "epsilon5" )
     ref( "pi" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"mu n (s m) k", muSc)


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
        "Ant_0" -> hof"E(0, f(k, x))",
        "Ant_1" -> hof"TopFuncDef(0, k, g(x))",
        "Ant_2" -> hof"iLEQ(x, g(x))",
        "Ant_3" -> hof"?x CutDistinct(0,0,x)" ),
      Seq( "Suc_2" -> hof"E(f(k, x), f(k, g(x)))" ) )
  val EpsilonBc = Lemma( esEpsilonBc ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_3"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1"
    allL( "Ant_3", le"(g x)" )
    orL
    impL
    trivial
    cut( "cut1", hof"E(0, f(k, (g x)))" )
    ref( "TransitivityE" )
    ref( "NumericTransitivity" )
    ref( "minimalElement" )
  }
  ctx += Context.ProofDefinitionDeclaration( le"epsilon 0 k 0 x", EpsilonBc )

  Sequent(
    Seq( hof"!x TopFuncDef(m, w,x)",
      hof"?x CutDistinct(k,n,x)"),
    Seq( hof"?x E(f(w, x), f(w, suc(x)))" ) )
  val esEpsilonSc =
    Sequent(
      Seq("Ant_1" -> hof"!x TopFuncDef((s m), k, x)",
        "Ant_3" -> hof"?x CutDistinct(k,0,x)" ),
      Seq( "Suc_2" -> hof"?x E(f(k, x), f(k, g(x)))" ) )
  val EpsilonSc = Lemma( esEpsilonSc ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_3"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1"
    andL
    allL( "Ant_3_1", le"(g x)" )
    orL( "Ant_3_1_0" )
    impL
    trivial
    orL
    cut( "cut1", hof"E(0, f(k, (g x)))" )
    ref( "TransitivityE" )
    ref( "NumericTransitivity" )
    ref( "epsilon" )
    ref( "minimalElement" )

  }
  ctx += Context.ProofDefinitionDeclaration( le"epsilon (s m) k w n", EpsilonSc)


}

