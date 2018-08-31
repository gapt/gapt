package gapt.examples

import gapt.expr._
import gapt.proofs.Sequent
import gapt.proofs.context.Context
import gapt.proofs.context.update.InductiveType
import gapt.proofs.context.update.{ PrimitiveRecursiveFunction => PrimRecFun }
import gapt.proofs.context.update.ProofDefinitionDeclaration
import gapt.proofs.context.update.ProofNameDeclaration
import gapt.proofs.context.update.Sort
import gapt.proofs.gaptic._

object ECSJumpSchema extends TacticsProof {
  ctx += InductiveType( "nat", hoc"0 : nat", hoc"s : nat>nat" )
  ctx += Sort( "i" )
  //Constants
  ctx += hoc"f:nat>i>nat"
  ctx += hoc"g:i>i"
  ctx += hoc"z:i"
  ctx += hoc"E: nat>nat>o"
  ctx += hoc"LE: nat>nat>o"
  ctx += hoc"iLEQ: i>i>o"
  //Proof Constants
  ctx += hoc"omega: nat>nat>nat"
  ctx += hoc"phi: nat>nat>nat"
  ctx += hoc"mu: nat>nat>i>nat"
  ctx += hoc"gamma: nat>nat>nat>i>nat"
  ctx += hoc"epsilon: nat>nat>nat>i>nat"
  ctx += hoc"theta: nat>nat>nat>i>nat"
  ctx += hoc"delta: nat>nat>nat>i>nat"
  ctx += hoc"beta: nat>nat>nat>i>nat"
  ctx += hoc"alpha: nat>nat>nat>i>i>nat"
  ctx += hoc"zeta: nat>nat>nat>i>nat"
  ctx += hoc"pi:nat>nat>nat>i>nat"
  ctx += hoc"sigma:nat>nat>nat>i>i>nat"
  ctx += hoc"psi:nat>nat>nat>i>nat"
  ctx += hoc"xi:nat>nat>nat>i>nat"
  ctx += hoc"chi:nat>nat>nat>i>nat"

  //defined predicate symbols
  ctx += PrimRecFun( hoc"POR:nat>nat>i>o", "POR 0 m x = E 0 (f m x) ", "POR (s y) m x = (E (s y) (f m x) ∨ POR y m x)" )
  ctx += PrimRecFun( hoc"PAND:nat>nat>o", "(PAND 0 n)= (∀x (POR n 0 x))", "(PAND (s m) n) = ((∀x (POR n (s m) x)) & (PAND m n))" )
  ctx += PrimRecFun( hoc"TopFuncDef:nat>nat>i>o", "(TopFuncDef 0 k x)= (E (f 0 x) (f k x)) ", "(TopFuncDef (s m) k x)= ((E (f (s m) x) (f k x)) | (TopFuncDef m k x))" )
  ctx += PrimRecFun(
    hoc"CutDistinct:nat>nat>i>o",
    "(CutDistinct 0 n x) =  (∀y (((iLEQ x y) -> (E n (f 0 y))) | (LE (f 0 y) n) ))",
    "(CutDistinct (s m) n x) = (" +
      "(CutDistinct m n x) &  (∀y (((iLEQ x y) -> (E n (f (s m) y))) | (LE (f (s m) y) n))))" )
  ctx += PrimRecFun(
    hoc"CutConstant:nat>nat>i>o",
    "(CutConstant 0 n x) =  (∀y ((iLEQ x y) -> (E n (f 0 y))))",
    "(CutConstant (s m) n x) = ((CutConstant m n x) &  (∀y ((iLEQ x y) -> (E n (f (s m) y)))))" )
  ctx += PrimRecFun(
    hoc"CutLess:nat>nat>i>o",
    "(CutLess 0 n x) =  (LE (f 0 x) n)",
    "(CutLess (s m) n x) = ((CutLess m n x) | (LE (f (s m) x) n))" )

  //Axioms
  ctx += "LEDefinition" -> hos"POR(n,m,a) :- LE(f(m,a), s(n))"
  ctx += "NumericTransitivity" -> hos"E(n,f(m,a)),E(n,f(m,g(a))) :- E(f(m,a), f(m,g(a)))"
  ctx += "TransitivityE" -> hos"E(a,b),E(b,c) :- E(a,c)"
  ctx += "TransitivityiLEQ" -> hos"iLEQ(a,b),iLEQ(b,c) :-  iLEQ(a,c) "
  ctx += "minimalElement" -> hos"LE(n,0) :- "
  ctx += "reflexivity" -> hos" :- iLEQ(a,a)"
  ctx += "ordCondition" -> hos"LE(f(m,a),s(n)),iLEQ(a,b) :- E(n,f(k,b)), LE(f(k,b),n)"

  //End sequents of LKS proofs
  val esOmega = Sequent(
    Seq( hof"PAND(m,n)", hof"!x( TopFuncDef(m,s(m),x))" ),
    Seq( hof"?x (iLEQ(x,g(x)) -> E(f(s(m),x), f(s(m),g(x))) )" ) )
  ctx += ProofNameDeclaration( le"omega n m", esOmega )
  val esPhi = Sequent(
    Seq( hof"?x CutDistinct(m,n,x)", hof"!x( TopFuncDef(m,s(m),x))" ),
    Seq( hof"?x (iLEQ(x,g(x)) -> E(f(s(m),x), f(s(m),g(x))) )" ) )
  ctx += ProofNameDeclaration( le"phi n m", esPhi )
  val esMu = Sequent(
    Seq( hof"PAND(m,n)" ),
    Seq( hof"CutDistinct(m,n,x)" ) )
  ctx += ProofNameDeclaration( le"mu m n x", esMu )
  val esGamma = Sequent(
    Seq(
      hof"TopFuncDef(m, k, g(x))",
      hof"TopFuncDef(m, k, x)",
      hof"iLEQ(x, g(x))",
      hof"CutDistinct(m,n,x)" ),
    Seq( hof"E(f(k, x), f(k, g(x)))" ) )
  ctx += ProofNameDeclaration( le"gamma m k n x", esGamma )
  val esEpsilon = Sequent(
    Seq(
      hof"E(0, f(k, x))",
      hof"TopFuncDef(m, k, g(x))",
      hof"iLEQ(x, g(x))",
      hof"CutDistinct(m,n,x)" ),
    Seq( hof"E(f(k, x), f(k, g(x)))" ) )
  ctx += ProofNameDeclaration( le"epsilon m k n x", esEpsilon )
  val estheta = Sequent(
    Seq(
      hof"E(0, f(k, g(x)))",
      hof"TopFuncDef(m, k, x)",
      hof"iLEQ(x, g(x))",
      hof"CutDistinct(m,n,x)" ),
    Seq( hof"E(f(k, x), f(k, g(x)))" ) )
  ctx += ProofNameDeclaration( le"theta m k n x", estheta )
  val esdelta = Sequent(
    Seq( hof" CutDistinct(m,s(n),y)" ),
    Seq(
      hof"CutDistinct(m,n,y)",
      hof"?x CutConstant(m,s(n),x)",
      hof"?x CutLess(k,s(n),x)" ) )
  ctx += ProofNameDeclaration( le"delta n m k y", esdelta )
  val esbeta = Sequent(
    Seq( hof"CutLess(k,s(n),x)" ),
    Seq( hof"CutDistinct(m,n,x)" ) )
  ctx += ProofNameDeclaration( le"beta m n k x", esbeta )
  val esalpha = Sequent(
    Seq(
      hof"CutLess(k, s(n), x)",
      hof"iLEQ(x, y)" ),
    Seq(
      hof"E(n, f(m, y))",
      hof"LE(f(m, y), n)" ) )
  ctx += ProofNameDeclaration( le"alpha k n m x y", esalpha )
  val eszeta = Sequent(
    Seq(
      hof"CutConstant(m,n,x)",
      hof"iLEQ(x,g(x))",
      hof"TopFuncDef(m, k, x)",
      hof"TopFuncDef(m, k, g(x))" ),
    Seq( hof" E(f(k,x), f(k,g(x))) " ) )
  ctx += ProofNameDeclaration( le"zeta n m k x", eszeta )
  val espi = Sequent(
    Seq( hof"LE(f(m, x), n)" ),
    Seq( hof"CutLess(k, n, x)" ) )
  ctx += ProofNameDeclaration( le"pi k n m x", espi )
  val essigma = Sequent(
    Seq(
      hof"CutDistinct(m, n, x)",
      hof"iLEQ(x,y)" ),
    Seq(
      hof"?z CutLess(k, n, z)",
      hof"CutConstant(m, n, y)" ) )
  ctx += ProofNameDeclaration( le"sigma n m k x y", essigma )
  val espsi = Sequent(
    Seq( hof"CutDistinct(m, n, x)" ),
    Seq(
      hof"?z CutLess(k, n, z)",
      hof"CutConstant(m, n, x)" ) )
  ctx += ProofNameDeclaration( le"psi n m k x", espsi )
  val esxi = Sequent(
    Seq(
      hof"E(n, f(k, x))",
      hof"CutConstant(m, n, x)",
      hof"iLEQ(x, g(x))",
      hof"TopFuncDef(m, k, g(x))" ),
    Seq( hof"E(f(k, x), f(k, g(x)))" ) )
  ctx += ProofNameDeclaration( le"xi n m k x", esxi )
  val eschi = Sequent(
    Seq(
      hof"E(n, f(k, g(x)))",
      hof"CutConstant(m, n, x)",
      hof"iLEQ(x, g(x))",
      hof"TopFuncDef(m, k, x)" ),
    Seq( hof"E(f(k, x), f(k, g(x)))" ) )
  ctx += ProofNameDeclaration( le"chi n m k x", eschi )
  //This is the top symbols of the proof schema which is only recursive in
  //n

  /*

               **************
             ***             ***
           ***                 ***
         ***                     ***
       ***                         ***
     ***                             ***
   ***                                 ***
   ***                                 ***
     ***                             ***
       ***                         ***
         ***                     ***
           ***                 ***
             ***             ***
      **********             **********
      **********             **********
   */
  val esOmegaBc =
    Sequent(
      Seq(
        "Ant_0" -> hof"PAND(m,0)",
        "Ant_1" -> hof"!x( TopFuncDef(m,s(m),x))" ),
      Seq( "Suc_0" -> hof"?x (iLEQ(x,g(x)) -> E(f(s(m),x), f(s(m),g(x))) )" ) )
  val omegaBc = Lemma( esOmegaBc ) {
    cut( "cut", hof"?x CutDistinct(m,0,x)" )
    exR( "cut", hoc"z" )
    ref( "mu" )
    ref( "phi" )
  }
  ctx += ProofDefinitionDeclaration( le"omega 0 m", omegaBc )

  val esOmegaSc =
    Sequent(
      Seq(
        "Ant_0" -> hof"PAND(m,s(n))",
        "Ant_1" -> hof"!x( TopFuncDef(m,s(m),x))" ),
      Seq( "Suc_0" -> hof"?x (iLEQ(x,g(x)) -> E(f(s(m),x), f(s(m),g(x))) )" ) )
  val omegaSc = Lemma( esOmegaSc ) {
    cut( "cut", hof"?x CutDistinct(m,s(n),x)" )
    exR( "cut", hoc"z" )
    ref( "mu" )
    ref( "phi" )
  }
  ctx += ProofDefinitionDeclaration( le"omega (s n) m", omegaSc )

  /*
       ************************
       ************************
                 ****
                 ****
                 ****
                 ****
               ********
             ***  **  ***
           ***    **    ***
         ***      **      ***
         ***      **      ***
           ***    **    ***
             ***  **  ***
               ********
                 ****
                 ****
                 ****
                 ****
       ************************
       ************************

   */
  val esPhiBc =
    Sequent(
      Seq(
        "Ant_0" -> hof"?x CutDistinct(0,0,x)",
        "Ant_1" -> hof"!x( TopFuncDef(0,s(0),x))" ),
      Seq( "Suc_0" -> hof"?x (iLEQ(x,g(x)) -> E(f(s(0),x), f(s(0),g(x))) )" ) )
  val phiBc = Lemma( esPhiBc ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_0"
    exL( fov"a" )
    allL( "Ant_0", fov"a" )
    exR( fov"a" )
    allL( "Ant_0", le"(g a)" )
    impR
    orL( "Ant_0_0" )
    orL( "Ant_0_1" )
    impL( "Ant_0_0" )
    ref( "reflexivity" )
    impL( "Ant_0_1" )
    trivial
    allL( "Ant_1", le"(g a)" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_0"
    cut( "cut1", hof"E(0, f(s(0), g(a)))" )
    ref( "TransitivityE" )
    cut( "cut2", hof"E(0, f(s(0), a))" )
    allL( "Ant_1", le"a" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
    ref( "TransitivityE" )
    ref( "NumericTransitivity" )
    ref( "minimalElement" )
    ref( "minimalElement" )
  }
  ctx += ProofDefinitionDeclaration( le"phi 0 0", phiBc )

  //There are a total of three step cases for phi
  val esPhiSc1 =
    Sequent(
      Seq(
        "Ant_0" -> hof"?x CutDistinct(0,s(n),x)",
        "Ant_1" -> hof"!x( TopFuncDef(0,s(0),x))" ),
      Seq( "Suc_0" -> hof"?x (iLEQ(x,g(x)) -> E(f(s(0),x), f(s(0),g(x))) )" ) )
  val phiSc1 = Lemma( esPhiSc1 ) {
    cut( "cut", hof"?x CutDistinct(0,n,x)" )
    cut( "cut1", hof"?x !y ( iLEQ(x,y) -> E(s(n),f(0,y)) )" )
    cut( "cut2", hof"?x ( LE(f(0,x),s(n)) )" )
    unfold( "CutDistinct" ) atMost 1 in "Ant_0"
    exL( fov"a" )
    exR( "cut1", fov"a" )
    allR( "cut1_0", fov"b" )
    allL( "Ant_0", fov"b" )
    exR( "cut2", fov"b" )
    impR
    orL
    impL
    trivial
    trivial
    trivial
    exL( "cut2", fov"a" )
    unfold( "CutDistinct" ) atMost 1 in "cut"
    exR( "cut", fov"a" )
    allR( "cut_0", fov"b" )
    orR
    impR
    ref( "ordCondition" )
    exL( "cut1", fov"a" )
    allL( "cut1", fov"a" )
    allL( "cut1", le"(g a)" )
    exR( "Suc_0", fov"a" )
    impL( "cut1_1" )
    impL
    impR
    trivial
    impR
    trivial
    impL( "cut1_0" )
    ref( "reflexivity" )
    impR
    allL( "Ant_1", le"(g a)" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_0"
    cut( "cut11", hof"E(s(n), f(s(0), g(a)))" )
    ref( "TransitivityE" )
    cut( "cut22", hof"E(s(n), f(s(0), a))" )
    allL( "Ant_1", le"a" )
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1_1"
    ref( "TransitivityE" )
    ref( "NumericTransitivity" )
    ref( "phi" )
  }
  ctx += ProofDefinitionDeclaration( le"phi (s n) 0", phiSc1 )

  val esPhiSc2 =
    Sequent(
      Seq(
        "Ant_0" -> hof"?x CutDistinct(s(m),0,x)",
        "Ant_1" -> hof"!x( TopFuncDef(s(m),s(s(m)),x))" ),
      Seq( "Suc_0" -> hof"?x (iLEQ(x,g(x)) -> E(f(s(s(m)),x), f(s(s(m)),g(x))) )" ) )
  val phiSc2 = Lemma( esPhiSc2 ) {
    exL( fov"a" )
    exR( fov"a" )
    impR
    allL( "Ant_1", fov"a" )
    allL( "Ant_1", le"(g a)" )
    ref( "gamma" )
  }
  ctx += ProofDefinitionDeclaration( le"phi 0  (s m)", phiSc2 )

  val esPhiSc3 =
    Sequent(
      Seq(
        "Ant_0" -> hof"?x CutDistinct(s(m),s(n),x)",
        "Ant_1" -> hof"!x( TopFuncDef(s(m),s(s(m)),x))" ),
      Seq( "Suc_0" -> hof"?x (iLEQ(x,g(x)) -> E(f(s(s(m)),x), f(s(s(m)),g(x))) )" ) )
  val phiSc3 = Lemma( esPhiSc3 ) {
    cut( "cutn", hof"?x CutDistinct(s(m),n,x)" )
    cut( "cutcon", hof"?x CutConstant(s(m),s(n),x)" )
    cut( "cutless", hof"?x CutLess(s(m),s(n),x)" )
    focus( 3 )
    ref( "phi" )
    exL( "Ant_0", fov"a" )
    exR( "cutn", fov"a" )
    exR( "cutcon", fov"a" )
    ref( "delta" )
    exL( "cutless", fov"a" )
    exR( "cutcon", fov"a" )
    exR( "cutn", fov"a" )
    ref( "beta" )
    exL( "cutcon", fov"a" )
    exR( "Suc_0", fov"a" )
    impR
    allL( "Ant_1", fov"a" )
    allL( "Ant_1", le"(g a)" )
    ref( "zeta" )
  }
  ctx += ProofDefinitionDeclaration( le"phi (s n) (s m)", phiSc3 )

  /*
             ****          ****
              **            **
              **            **
              **            **
              **            **
              ****        ****
              **  **     ** **
              **   **  **   **
              **    ****    ***
              **
               **
                **

   */
  val esMuBc2 =
    Sequent(
      Seq( "Ant_0" -> hof"PAND(0,0)" ),
      Seq( "Suc_0" -> hof"CutDistinct(0,0,x)" ) )
  val muBc2 = Lemma( esMuBc2 ) {
    unfold( "CutDistinct" ) atMost 1 in "Suc_0"
    unfold( "PAND" ) atMost 1 in "Ant_0"
    unfold( "POR" ) atMost 1 in "Ant_0"
    allR( "Suc_0", fov"a" )
    orR
    impR
    allL( "Ant_0", fov"a" )
    trivial
  }
  ctx += ProofDefinitionDeclaration( le"mu 0 0 x", muBc2 )
  val esMuSc2 =
    Sequent(
      Seq( "Ant_0" -> hof"PAND(s(m),0)" ),
      Seq( "Suc_0" -> hof" CutDistinct(s(m),0,x)" ) )
  val muSc2 = Lemma( esMuSc2 ) {
    unfold( "PAND" ) atMost 1 in "Ant_0"
    unfold( "CutDistinct" ) atMost 1 in "Suc_0"
    andL
    andR
    ref( "mu" )
    allR( "Suc_0", fov"a" )
    orR
    impR
    allL( "Ant_0_0", fov"a" )
    unfold( "POR" ) atMost 1 in "Ant_0_0_0"
    trivial
  }
  ctx += ProofDefinitionDeclaration( le"mu (s m) 0 x", muSc2 )

  val esMuBc =
    Sequent(
      Seq( "Ant_0" -> hof"PAND(0,(s n))" ),
      Seq( "Suc_0" -> hof"CutDistinct(0,(s n),x)" ) )
  val muBc = Lemma( esMuBc ) {
    unfold( "PAND" ) atMost 1 in "Ant_0"
    unfold( "POR" ) atMost 1 in "Ant_0"
    unfold( "CutDistinct" ) atMost 1 in "Suc_0"
    allR( "Suc_0", fov"a" )
    orR
    impR
    allL( "Ant_0", fov"a" )
    orL
    trivial
    ref( "LEDefinition" )
  }
  ctx += ProofDefinitionDeclaration( le"mu 0 (s n) x", muBc )

  val esMuSc =
    Sequent(
      Seq( "Ant_0" -> hof"PAND(s(m),s(n))" ),
      Seq( "Suc_0" -> hof"CutDistinct(s(m),s(n),x)" ) )
  val muSc = Lemma( esMuSc ) {
    unfold( "PAND" ) atMost 1 in "Ant_0"
    andL
    unfold( "POR" ) atMost 1 in "Ant_0_0"
    unfold( "CutDistinct" ) atMost 1 in "Suc_0"
    andR
    ref( "mu" )
    allR( "Suc_0", fov"a" )
    orR
    impR
    allL( "Ant_0_0", fov"a" )
    orL
    trivial
    ref( "LEDefinition" )
  }
  ctx += ProofDefinitionDeclaration( le"mu (s m) (s n) x", muSc )

  /*

                         ********
                        **********
                       ***      ***
                      ***        ***
                     ***          ***
                    ******************
                    ******************
                     ***          ***
                      ***        ***
                       ***      ***
                        **********
                         ********
 */
  val esthetaBc =
    Sequent(
      Seq(
        "Ant_0" -> hof"E(0, f(k, g(x)))",
        "Ant_1" -> hof"TopFuncDef(0, k, x)",
        "Ant_2" -> hof"iLEQ(x, g(x))",
        "Ant_3" -> hof"CutDistinct(0,0,x)" ),
      Seq( "Suc_2" -> hof"E(f(k, x), f(k, g(x)))" ) )
  val thetaBc = Lemma( esthetaBc ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_3"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1"
    allL( "Ant_3", le"x" )
    orL
    impL
    ref( "reflexivity" )
    cut( "cut1", hof"E(0, f(k, x))" )
    ref( "TransitivityE" )
    ref( "NumericTransitivity" )
    ref( "minimalElement" )
  }
  ctx += ProofDefinitionDeclaration( le"theta 0 k 0 x", thetaBc )

  val esthetaBc2 =
    Sequent(
      Seq(
        "Ant_0" -> hof"E(0, f(k, g(x)))",
        "Ant_1" -> hof"TopFuncDef((s m), k, x)",
        "Ant_2" -> hof"iLEQ(x, g(x))",
        "Ant_3" -> hof"CutDistinct((s m),0,x)" ),
      Seq( "Suc_2" -> hof"E(f(k, x), f(k, g(x)))" ) )
  val thetaBc2 = Lemma( esthetaBc2 ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_3"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1"
    andL
    allL( "Ant_3_1", le"x" )
    orL( "Ant_3_1_0" )
    impL
    ref( "reflexivity" )
    orL
    cut( "cut1", hof"E(0, f(k, x))" )
    ref( "TransitivityE" )
    ref( "NumericTransitivity" )
    ref( "theta" )
    ref( "minimalElement" )

  }
  ctx += ProofDefinitionDeclaration( le"theta (s m) k 0 x", thetaBc2 )

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
        "Ant_3" -> hof"CutDistinct(0,0,x)" ),
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
  ctx += ProofDefinitionDeclaration( le"epsilon 0 k 0 x", EpsilonBc )

  val esEpsilonBc2 =
    Sequent(
      Seq(
        "Ant_0" -> hof"E(0, f(k, x))",
        "Ant_1" -> hof"TopFuncDef((s m), k, g(x))",
        "Ant_2" -> hof"iLEQ(x, g(x))",
        "Ant_3" -> hof"CutDistinct((s m),0,x)" ),
      Seq( "Suc_2" -> hof"E(f(k, x), f(k, g(x)))" ) )
  val EpsilonBc2 = Lemma( esEpsilonBc2 ) {
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
  ctx += ProofDefinitionDeclaration( le"epsilon (s m) k 0 x", EpsilonBc2 )

  /*

                       ****************
                       ****************
                       **            **
                       **           ****
                       **
                       **
                       **
                       **
                       **
                      ****
   */
  val esGammaBc =
    Sequent(
      Seq(
        "Ant_0" -> hof"TopFuncDef(0, k, g(x))",
        "Ant_1" -> hof"TopFuncDef(0, k, x)",
        "Ant_2" -> hof"iLEQ(x, g(x))",
        "Ant_3" -> hof"CutDistinct(0,0,x)" ),
      Seq( "Suc_2" -> hof"E(f(k, x), f(k, g(x)))" ) )
  val GammaBc = Lemma( esGammaBc ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_3"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_0"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1"
    allL( "Ant_3", le"x" )
    orL
    impL
    ref( "reflexivity" )
    cut( "cut1", hof"E(0, f(k, x))" )
    ref( "TransitivityE" )
    allL( "Ant_3", le"(g x)" )
    orL
    impL
    trivial
    cut( "cut2", hof"E(0, f(k, g(x)))" )
    ref( "TransitivityE" )
    ref( "NumericTransitivity" )
    ref( "minimalElement" )
    ref( "minimalElement" )
  }
  ctx += ProofDefinitionDeclaration( le"gamma 0 k 0 x", GammaBc )

  val esGammaBc2 =
    Sequent(
      Seq(
        "Ant_0" -> hof"TopFuncDef(s(m), k, g(x))",
        "Ant_1" -> hof"TopFuncDef(s(m), k, x)",
        "Ant_2" -> hof"iLEQ(x, g(x))",
        "Ant_3" -> hof"CutDistinct(s(m),0,x)" ),
      Seq( "Suc_2" -> hof"E(f(k, x), f(k, g(x)))" ) )
  val GammaBc2 = Lemma( esGammaBc2 ) {
    unfold( "TopFuncDef" ) atMost 1 in "Ant_0"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_1"
    orL( "Ant_0" )
    orL
    focus( 2 )
    orL
    focus( 1 )
    unfold( "CutDistinct" ) atMost 1 in "Ant_3"
    andL
    ref( "gamma" )
    unfold( "CutDistinct" ) atMost 1 in "Ant_3"
    andL
    allL( "Ant_3_1", le"x" )
    orL
    impL
    ref( "reflexivity" )
    focus( 1 )
    ref( "minimalElement" )
    cut( "cut1", hof"E(0, f(k, x))" )
    ref( "TransitivityE" )
    ref( "epsilon" )
    unfold( "CutDistinct" ) atMost 1 in "Ant_3"
    andL
    allL( "Ant_3_1", le"x" )
    orL
    impL
    ref( "reflexivity" )
    allL( "Ant_3_1", le"(g x)" )
    orL
    impL
    trivial
    cut( "cut1", hof"E(0, f(k, x))" )
    ref( "TransitivityE" )
    cut( "cut2", hof"E(0, f(k,(g x)))" )
    ref( "TransitivityE" )
    ref( "NumericTransitivity" )
    ref( "minimalElement" )
    ref( "minimalElement" )
    unfold( "CutDistinct" ) atMost 1 in "Ant_3"
    andL
    allL( "Ant_3_1", le"(g x)" )
    orL
    impL
    trivial
    cut( "cut2", hof"E(0, f(k,(g x)))" )
    ref( "TransitivityE" )
    ref( "theta" )
    ref( "minimalElement" )
  }
  ctx += ProofDefinitionDeclaration( le"gamma (s m) k 0 x", GammaBc2 )

  /*


                                  *
                                 ***
                                ** **
                               **   **
                              **     **
                             **       **
                            **         **
                           **           **
                          **             **
                         **               **
                        **                 **
                       **                   **
                      **                     **
                     **                       **
                    *****************************


 */
  val esdeltaBc =
    Sequent(
      Seq( "Ant_0" -> hof" CutDistinct(0,s(n),a)" ),
      Seq(
        "Suc_0" -> hof"?x CutConstant(0,s(n),x)",
        "Suc_1" -> hof" CutDistinct(0,n,a)",
        "Suc_2" -> hof"?x CutLess(k,s(n),x)" ) )
  val deltaBc = Lemma( esdeltaBc ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_0"
    unfold( "CutDistinct" ) atMost 1 in "Suc_1"
    allR( fov"b" )
    orR
    impR
    allL( fov"b" )
    orL
    impL
    trivial
    exR( "Suc_0", fov"b" )
    unfold( "CutConstant" ) atMost 1 in "Suc_0_0"
    allR( fov"c" )
    impR
    allL( fov"c" )
    orL
    impL
    ref( "TransitivityiLEQ" )
    trivial
    exR( "Suc_2", fov"c" )
    ref( "pi" )
    allL( "Ant_0", fov"a" )
    orL
    impL
    ref( "reflexivity" )
    exR( "Suc_2", fov"b" )
    ref( "pi" )
    ref( "ordCondition" )
  }
  ctx += ProofDefinitionDeclaration( le"delta n 0 k a", deltaBc )

  val esdeltaSc =
    Sequent(
      Seq( "Ant_0" -> hof" CutDistinct(s(m),s(n),a)" ),
      Seq(
        "Suc_0" -> hof"?x CutConstant(s(m),s(n),x)",
        "Suc_1" -> hof" CutDistinct(s(m),n,a)",
        "Suc_2" -> hof"?x CutLess(k,s(n),x)" ) )
  val deltaSc = Lemma( esdeltaSc ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_0"
    unfold( "CutDistinct" ) atMost 1 in "Ant_0"
    unfold( "CutDistinct" ) atMost 1 in "Suc_1"
    andR
    focus( 1 )
    allR( fov"b" )
    orR
    impR
    andL
    exR( "Suc_0", fov"b" )
    unfold( "CutConstant" ) atMost 1 in "Suc_0_0"
    andR
    focus( 1 )
    allR( fov"c" )
    impR
    allL( fov"c" )
    orL
    impL
    ref( "TransitivityiLEQ" )
    trivial
    exR( "Suc_2", fov"c" )
    ref( "pi" )
    ref( "sigma" )
    andL
    exR( "Suc_0", fov"a" )
    unfold( "CutConstant" ) atMost 1 in "Suc_0_0"
    andR
    focus( 1 )
    allR( fov"b" )
    impR
    allL( fov"b" )
    orL
    impL
    trivial
    trivial
    exR( "Suc_2", fov"b" )
    ref( "pi" )
    ref( "psi" )
  }
  ctx += ProofDefinitionDeclaration( le"delta n (s m) k a", deltaSc )

  /*
           **************************
          ***************************
               ***               ***
               ***               ***
               ***               ***
               ***               ***
               ***               ***
               ***               ***
               ***               ***
               ***               ***
               ***               ***
               ***                **
               ***                 **
               ***                  **
   */

  val esPiBc =
    Sequent(
      Seq( "Ant_0" -> hof"LE(f(0, a), n)" ),
      Seq( "Suc_0" -> hof"CutLess(0, n, a)" ) )
  val PiBc = Lemma( esPiBc ) {
    unfold( "CutLess" ) atMost 1 in "Suc_0"
    trivial
  }
  ctx += ProofDefinitionDeclaration( le"pi 0 n 0 a", PiBc )

  val esPiBc2 =
    Sequent(
      Seq( "Ant_0" -> hof"LE(f(s(k), a), n)" ),
      Seq( "Suc_0" -> hof"CutLess(s(k), n, a)" ) )
  val PiBc2 = Lemma( esPiBc2 ) {
    unfold( "CutLess" ) atMost 1 in "Suc_0"
    orR
    trivial
  }
  ctx += ProofDefinitionDeclaration( le"pi (s k) n (s k)  a", PiBc2 )

  val esPiSc =
    Sequent(
      Seq( "Ant_0" -> hof"LE(f(m, a), n)" ),
      Seq( "Suc_0" -> hof"CutLess(s(k), n, a)" ) )
  val PiSc = Lemma( esPiSc ) {
    unfold( "CutLess" ) atMost 1 in "Suc_0"
    orR
    ref( "pi" )
  }
  ctx += ProofDefinitionDeclaration( le"pi (s k) n m  a", PiSc )

  /*
       *************************
       *************************
       ***                    **
         ***                   *
           ***
             ***
               ***
                 ***
               ***
             ***
           ***
         ***                   *
       ***                    **
       *************************
       *************************
 */

  val esSigmaBc =
    Sequent(
      Seq(
        "Ant_0" -> hof"CutDistinct(0, n, a)",
        "Ant_1" -> hof"iLEQ(a,b)" ),
      Seq(
        "Suc_0" -> hof"?z CutLess(k, n, z)",
        "Suc_1" -> hof"CutConstant(0, n, b)" ) )
  val SigmaBc = Lemma( esSigmaBc ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_0"
    unfold( "CutConstant" ) atMost 1 in "Suc_1"
    allR( fov"c" )
    impR
    allL( fov"c" )
    orL
    impL
    ref( "TransitivityiLEQ" )
    trivial
    exR( fov"c" )
    ref( "pi" )
  }
  ctx += ProofDefinitionDeclaration( le"sigma n 0 k a b", SigmaBc )

  val esSigmaSc =
    Sequent(
      Seq(
        "Ant_0" -> hof"CutDistinct(s(m), n, a)",
        "Ant_1" -> hof"iLEQ(a,b)" ),
      Seq(
        "Suc_0" -> hof"?z CutLess(k, n, z)",
        "Suc_1" -> hof"CutConstant(s(m), n, b)" ) )
  val SigmaSc = Lemma( esSigmaSc ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_0"
    andL
    unfold( "CutConstant" ) atMost 1 in "Suc_1"
    andR
    ref( "sigma" )
    allR( fov"c" )
    impR
    allL( fov"c" )
    orL
    impL
    ref( "TransitivityiLEQ" )
    trivial
    exR( fov"c" )
    ref( "pi" )
  }
  ctx += ProofDefinitionDeclaration( le"sigma n (s m) k a b", SigmaSc )

  /*
     *          *****          *
     **          ***          **
     ***         ***         ***
      ***        ***        ***
      ****       ***       ****
       ****      ***      ****
        ****     ***     ****
         *****   ***   *****
          *****************
          *****************
                *****
                 ***
                 ***
                 ***
                 ***
                 ***
                 ***
                *****
               *******
  */

  val esPsiBc =
    Sequent(
      Seq( "Ant_0" -> hof"CutDistinct(0, n, a)" ),
      Seq(
        "Suc_0" -> hof"?z CutLess(k, n, z)",
        "Suc_1" -> hof"CutConstant(0, n, a)" ) )
  val PsiBc = Lemma( esPsiBc ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_0"
    unfold( "CutConstant" ) atMost 1 in "Suc_1"
    allR( fov"b" )
    impR
    allL( fov"b" )
    orL
    impL
    trivial
    trivial
    exR( fov"b" )
    ref( "pi" )
  }
  ctx += ProofDefinitionDeclaration( le"psi n 0 k a", PsiBc )

  val esPsiSc =
    Sequent(
      Seq( "Ant_0" -> hof"CutDistinct(s(m), n, a)" ),
      Seq(
        "Suc_0" -> hof"?z CutLess(k, n, z)",
        "Suc_1" -> hof"CutConstant(s(m), n, a)" ) )
  val PsiSc = Lemma( esPsiSc ) {
    unfold( "CutDistinct" ) atMost 1 in "Ant_0"
    andL
    unfold( "CutConstant" ) atMost 1 in "Suc_1"
    andR
    ref( "psi" )
    allR( fov"b" )
    impR
    allL( fov"b" )
    orL
    impL
    trivial
    trivial
    exR( fov"b" )
    ref( "pi" )
  }
  ctx += ProofDefinitionDeclaration( le"psi n (s m) k a", PsiSc )

  val esZetaBc =
    Sequent(
      Seq(
        "Ant_0" -> hof"CutConstant(0,n,a)",
        "Ant_1" -> hof"iLEQ(a,g(a))",
        "Ant_2" -> hof"TopFuncDef(0, k, a)",
        "Ant_3" -> hof"TopFuncDef(0, k, g(a))" ),
      Seq( "Suc_0" -> hof" E(f(k,a), f(k,g(a))) " ) )
  val ZetaBc = Lemma( esZetaBc ) {
    unfold( "CutConstant" ) atMost 1 in "Ant_0"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_2"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_3"
    allL( "Ant_0", fov"a" )
    impL
    ref( "reflexivity" )
    cut( "cut2", hof"E(n, f(k,a))" )
    ref( "TransitivityE" )
    allL( "Ant_0", le"(g a)" )
    impL
    trivial
    cut( "cut2", hof"E(n, f(k,g(a)))" )
    ref( "TransitivityE" )
    ref( "NumericTransitivity" )
  }
  ctx += ProofDefinitionDeclaration( le"zeta n 0 k a", ZetaBc )

  val esZetaSc =
    Sequent(
      Seq(
        "Ant_0" -> hof"CutConstant(s(m),n,a)",
        "Ant_1" -> hof"iLEQ(a,g(a))",
        "Ant_2" -> hof"TopFuncDef(s(m), k, a)",
        "Ant_3" -> hof"TopFuncDef(s(m), k, g(a))" ),
      Seq( "Suc_0" -> hof" E(f(k,a), f(k,g(a))) " ) )
  val ZetaSc = Lemma( esZetaSc ) {
    unfold( "CutConstant" ) atMost 1 in "Ant_0"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_2"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_3"
    andL
    allL( "Ant_0_1", fov"a" )
    orL( "Ant_2" )
    impL
    ref( "reflexivity" )
    cut( "cut2", hof"E(n, f(k,a))" )
    ref( "TransitivityE" )
    orL
    allL( "Ant_0_1", le"(g a)" )
    impL
    trivial
    cut( "cut2", hof"E(n, f(k,g(a)))" )
    ref( "TransitivityE" )
    ref( "NumericTransitivity" )
    ref( "xi" )
    orL
    allL( "Ant_0_1", le"(g a)" )
    impL( "Ant_0_1_1" )
    trivial
    cut( "cut2", hof"E(n, f(k,g(a)))" )
    ref( "TransitivityE" )
    ref( "chi" )
    ref( "zeta" )

  }
  ctx += ProofDefinitionDeclaration( le"zeta n (s m) k a", ZetaSc )

  val esXiBc =
    Sequent(
      Seq(
        "Ant_0" -> hof"CutConstant(0,n,a)",
        "Ant_1" -> hof"iLEQ(a,g(a))",
        "Ant_2" -> hof"E(n, f(k, a))",
        "Ant_3" -> hof"TopFuncDef(0, k, g(a))" ),
      Seq( "Suc_0" -> hof" E(f(k,a), f(k,g(a))) " ) )
  val xiBc = Lemma( esXiBc ) {
    unfold( "CutConstant" ) atMost 1 in "Ant_0"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_3"
    allL( "Ant_0", le"(g a)" )
    impL
    trivial
    cut( "cut2", hof"E(n, f(k,g(a)))" )
    ref( "TransitivityE" )
    ref( "NumericTransitivity" )
  }
  ctx += ProofDefinitionDeclaration( le"xi n 0 k a", xiBc )

  val esXiSc =
    Sequent(
      Seq(
        "Ant_0" -> hof"CutConstant(s(m),n,a)",
        "Ant_1" -> hof"iLEQ(a,g(a))",
        "Ant_2" -> hof"E(n, f(k, a))",
        "Ant_3" -> hof"TopFuncDef(s(m), k, g(a))" ),
      Seq( "Suc_0" -> hof" E(f(k,a), f(k,g(a))) " ) )
  val xiSc = Lemma( esXiSc ) {
    unfold( "CutConstant" ) atMost 1 in "Ant_0"
    andL
    unfold( "TopFuncDef" ) atMost 1 in "Ant_3"
    orL
    allL( "Ant_0_1", le"(g a)" )
    impL
    trivial
    cut( "cut2", hof"E(n, f(k,g(a)))" )
    ref( "TransitivityE" )
    ref( "NumericTransitivity" )
    ref( "xi" )
  }
  ctx += ProofDefinitionDeclaration( le"xi n (s m) k a", xiSc )

  val esChiBc =
    Sequent(
      Seq(
        "Ant_0" -> hof"CutConstant(0,n,a)",
        "Ant_1" -> hof"iLEQ(a,g(a))",
        "Ant_2" -> hof"E(n, f(k, g(a)))",
        "Ant_3" -> hof"TopFuncDef(0, k, a)" ),
      Seq( "Suc_0" -> hof" E(f(k,a), f(k,g(a))) " ) )
  val chiBc = Lemma( esChiBc ) {
    unfold( "CutConstant" ) atMost 1 in "Ant_0"
    unfold( "TopFuncDef" ) atMost 1 in "Ant_3"
    allL( "Ant_0", le"a" )
    impL
    ref( "reflexivity" )
    cut( "cut2", hof"E(n, f(k,a))" )
    ref( "TransitivityE" )
    ref( "NumericTransitivity" )
  }
  ctx += ProofDefinitionDeclaration( le"chi n 0 k a", chiBc )

  val esChiSc =
    Sequent(
      Seq(
        "Ant_0" -> hof"CutConstant(s(m),n,a)",
        "Ant_1" -> hof"iLEQ(a,g(a))",
        "Ant_2" -> hof"E(n, f(k, g(a)))",
        "Ant_3" -> hof"TopFuncDef(s(m), k, a)" ),
      Seq( "Suc_0" -> hof" E(f(k,a), f(k,g(a))) " ) )
  val chiSc = Lemma( esChiSc ) {
    unfold( "CutConstant" ) atMost 1 in "Ant_0"
    andL
    unfold( "TopFuncDef" ) atMost 1 in "Ant_3"
    orL
    allL( "Ant_0_1", le"a" )
    impL
    ref( "reflexivity" )
    cut( "cut2", hof"E(n, f(k,a))" )
    ref( "TransitivityE" )
    ref( "NumericTransitivity" )
    ref( "chi" )
  }
  ctx += ProofDefinitionDeclaration( le"chi n (s m) k a", chiSc )

  val esBetaBc =
    Sequent(
      Seq( "Ant_0" -> hof"CutLess(k,s(n),a)" ),
      Seq( "Suc_0" -> hof"CutDistinct(0,n,a)" ) )
  val betaBc = Lemma( esBetaBc ) {
    unfold( "CutDistinct" ) atMost 1 in "Suc_0"
    allR( "Suc_0", fov"b" )
    orR
    impR
    ref( "alpha" )
  }
  ctx += ProofDefinitionDeclaration( le"beta 0 n k a", betaBc )

  val esBetaSc =
    Sequent(
      Seq( "Ant_0" -> hof"CutLess(k,s(n),a)" ),
      Seq( "Suc_0" -> hof"CutDistinct(s(m),n,a)" ) )
  val betaSc = Lemma( esBetaSc ) {
    unfold( "CutDistinct" ) atMost 1 in "Suc_0"
    andR
    ref( "beta" )
    allR( "Suc_0", fov"b" )
    orR
    impR
    ref( "alpha" )
  }
  ctx += ProofDefinitionDeclaration( le"beta (s m) n k a", betaSc )

  val esAlphaBc =
    Sequent(
      Seq(
        "Ant_0" -> hof"CutLess(0, s(n), a)",
        "Ant_1" -> hof"iLEQ(a,b)" ),
      Seq(
        "Suc_0" -> hof"E(n, f(m, b))",
        "Suc_1" -> hof"LE(f(m, b), n)" ) )
  val alphaBc = Lemma( esAlphaBc ) {
    unfold( "CutLess" ) atMost 1 in "Ant_0"
    ref( "ordCondition" )

  }
  ctx += ProofDefinitionDeclaration( le"alpha 0 n m a b", alphaBc )

  val esAlphaSc =
    Sequent(
      Seq(
        "Ant_0" -> hof"CutLess(s(k), s(n), a)",
        "Ant_1" -> hof"iLEQ(a,b)" ),
      Seq(
        "Suc_0" -> hof"E(n, f(m, b))",
        "Suc_1" -> hof"LE(f(m, b), n)" ) )
  val alphaSc = Lemma( esAlphaSc ) {
    unfold( "CutLess" ) atMost 1 in "Ant_0"
    orL
    ref( "alpha" )
    ref( "ordCondition" )

  }
  ctx += ProofDefinitionDeclaration( le"alpha (s k) n m a b", alphaSc )
}
