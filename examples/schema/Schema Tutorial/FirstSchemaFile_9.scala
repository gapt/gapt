import at.logic.gapt.expr._  
import at.logic.gapt.proofs.Context._ 
import at.logic.gapt.proofs.gaptic._ 
import at.logic.gapt.proofs.Context  
import at.logic.gapt.proofs.Sequent  

object FirstSchema extends TacticsProof {
  ctx += Context.InductiveType( "nat", hoc"0 : nat", hoc"s : nat>nat" )
  ctx += Context.Sort( "i" )

  ctx += hoc"E: nat>nat>o"
  ctx += hoc"LE: i>i>o"
  ctx += hoc"LEQ: i>i>o"

  ctx += hoc"f:i>nat"
  ctx += hoc"z:i"
  ctx += hoc"g:i>i"
  ctx += hoc"max:i>i>i"

  ctx += "efef" -> hcl"E(f(p),n),E(f(q),n) :- E(f(p),f(q))"
  ctx += "leq_refl" -> hos" :- LEQ(p,p)"
  ctx += "leq_g" -> hos"LEQ(g(p),q):- LE(p,q)"
  ctx += "leq_max1" -> hos"LEQ(max(a, b), c) :- LEQ(a, c)"
  ctx += "leq_max2" -> hos"LEQ(max(a, b), c) :- LEQ(b, c)"


  ctx += hoc"mu: nat>nat>nat"
  ctx += hoc"mubase: nat>nat"
  ctx += hoc"nu: nat>nat>i>nat"
  ctx += hoc"nuPrime:nat>i>nat"
  ctx += hoc"omega: nat>nat>nat"
  ctx += hoc"phi: nat>nat>nat"
  ctx += hoc"chi: nat>i>nat"

  ctx += PrimRecFun( hoc"POR:nat>i>o", "POR 0 x = E (f x) 0", "POR (s y) x = (E (f x) (s y) ∨ POR y x)" )
  ctx += PrimRecFun( hoc"Ech:nat>i>o", "Ech 0 x = (∃p ((LE x p) ∧  (E (f x) (f p))))", "Ech (s y) x = (∃p ((Ech y p) ∧ (LE x p) ∧  (E (f x) (f p))))" )

  
  
  




 val esnu = Sequent(Seq(hof"E(f(A),n)",hof"!x?y(LEQ(x,y) & E(f(y),n))" ),Seq( hof"Ech(m,A)" ) )
 val esmu = Sequent(Seq(hof"!x?y(LEQ(x,y) & E(f(y),n))" ),Seq( hof"?p Ech(m,p)" ) )
 val esmubase = Sequent(Seq(hof"!x?y(LEQ(x,y) & E(f(y),0))" ),Seq( hof"?p Ech(m,p)" ) )
 val eschi = Sequent(Seq( hof" POR(n,a) " ),Seq( hof"POR(n,a)" ) )
 val esnuPrime = Sequent(Seq(hof"E(f(A),0)",hof"!x?y(LEQ(x,y) & POR(0,y))" ),Seq( hof"Ech(m,A)" ) )
 val esOmega = Sequent(Seq(hof"!x POR(n,x)" ),Seq( hof"?p Ech(m,p)" ) ) 
 val esphi = Sequent(Seq(hof"!x?y (LEQ(x,y) & POR(n,y) )" ),Seq( hof"?p Ech(m,p)" ) )
 ctx += Context.ProofNameDeclaration( le"nu m n A", esnu ) // notice that here m is first than n
 ctx += Context.ProofNameDeclaration( le"mu m n", esmu ) // notice that here m is first than n
 ctx += Context.ProofNameDeclaration( le"mubase m", esmubase ) // notice that here there is only m
 ctx += Context.ProofNameDeclaration( le"chi n a", eschi ) // notice that here there is only n
 ctx += Context.ProofNameDeclaration( le"nuPrime m A", esnuPrime )// notice that here there is only m
 ctx += Context.ProofNameDeclaration( le"omega n m", esOmega )// notice that here n is first than m
 ctx += Context.ProofNameDeclaration( le"phi n m", esphi ) // notice that here n is first than m


 val esNuBc = Sequent(Seq(( "Ant_2" -> hof"E(f(A),n)" ),( "Ant_3" -> hof"!x?y(LEQ(x,y) & E(f(y),n))" ) ),Seq( ( "Suc_0" -> hof"Ech(0,A)" ) ) )
 val esNuSc = Sequent(Seq(( "Ant_2" -> hof"E(f(A),n)" ),( "Ant_3" -> hof"!x?y(LEQ(x,y) & E(f(y),n))" ) ),Seq( ( "Suc_0" -> hof"Ech(s(m),A)" ) ) )
 val esNuPrimeBc = Sequent(Seq(( "Ant_2" -> hof"E(f(A),0)" ),( "Ant_3" -> hof"!x?y(LEQ(x,y) & POR(0,y))" ) ),Seq( ( "Suc_0" -> hof"Ech(0,A)" ) ) )
 val esNuPrimeSc = Sequent(Seq(( "Ant_2" -> hof"E(f(A),0)" ),( "Ant_3" -> hof"!x?y(LEQ(x,y) & POR(0,y))" ) ),Seq( ( "Suc_0" -> hof"Ech(s(m),A)" ) ) )
 val esMuBc = Sequent(Seq(( "Ant_2" -> hof"!x?y(LEQ(x,y) & E(f(y),n))" ) ),Seq( ( "Suc_0" -> hof"?q Ech(0,q)" ) ) )
 val esMubaseBc = Sequent(Seq(( "Ant_2" -> hof"!x?y(LEQ(x,y) & E(f(y),0))" ) ),Seq( ( "Suc_0" -> hof"?q Ech(0,q)" ) ) )
 val esMubaseSc = Sequent(Seq(( "Ant_2" -> hof"!x?y(LEQ(x,y) & E(f(y),0))" ) ),Seq( ( "Suc_0" -> hof"?q Ech(s(m),q)" ) ) )
 val esMuSc = Sequent(Seq(( "Ant_2" -> hof"!x?y(LEQ(x,y) & E(f(y),n))" ) ),Seq( ( "Suc_0" -> hof"?q Ech(s(m),q)" ) ) )
 val esChiBc = Sequent(Seq( ( "Ant_2" -> hof" POR(0,a)" ) ),Seq(( "Suc_0" -> hof"POR(0,a)" ) ) )
 val esChiSc = Sequent(Seq(( "Ant_2" -> hof" POR(s(n),a)" ) ),Seq(( "Suc_0" -> hof"POR(s(n),a)" ) ) )

 val esphiBc = Sequent(Seq(( "Ant_2" -> hof"!x?y (LEQ(x,y) & POR(0,y))" ) ),Seq( ( "Suc_0" -> hof"?p Ech(m,p)" ) ) )
 val esOmegaBc = Sequent(Seq(( "Ant_2" -> hof"!x POR(0,x)" ) ),Seq( ( "Suc_0" -> hof"?p Ech(m,p)" ) ) )
 val esOmegaSc = Sequent(Seq(( "Ant_2" -> hof"!x POR(s(n),x)" ) ),Seq( ( "Suc_0" -> hof"?p Ech(m,p)" ) ) )

 
 val NuBc = Lemma( esNuBc ) {
    allL( "Ant_3", le"g(A)" )
    unfold( "Ech" ) atMost 1 in "Suc_0"
    exL( fov"B" )
    exR( fov"B" )
    andL
    andR
    foTheory
    foTheory
  }
  val NuSc = Lemma( esNuSc ) {
    allL( "Ant_3", le"g(A)" )
    unfold( "Ech" ) atMost 1 in "Suc_0"
    exL( fov"B" )
    exR( fov"B" )
    andL
    andR
    andR
    ref( "nu" )
    foTheory
    foTheory
  }
  val NuPrimeBc = Lemma( esNuPrimeBc ) {
    allL( "Ant_3", le"g(A)" )
    unfold( "Ech" ) atMost 1 in "Suc_0"
    exL( fov"B" )
    exR( fov"B" )
    andL
    andR
    foTheory
    unfold( "POR" ) atMost 1 in "Ant_3_0_1"
    foTheory
  }
  val NuPrimeSc = Lemma( esNuPrimeSc ) {
    allL( "Ant_3", le"g(A)" )
    unfold( "Ech" ) atMost 1 in "Suc_0"
    exL( fov"B" )
    exR( fov"B" )
    andL
    unfold( "POR" ) atMost 1 in "Ant_3_0_1"
    andR
    andR
    ref( "nuPrime" )
    foTheory
    foTheory

  }
  val muBc = Lemma( esMuBc ) {
    allL( "Ant_2", hoc"z:i" )
    exL( fov"B" )
    allL( "Ant_2", le"(g B)" )
    exL( fov"A" )
    exR( fov"B" )
    unfold( "Ech" ) atMost 1 in "Suc_0_0"
    exR( "Suc_0_0", fov"A" )
    andL( "Ant_2_1" )
    andL
    andR
    foTheory
    foTheory
  }
  val muSc = Lemma( esMuSc ) {
    allL( "Ant_2", hoc"z:i" )
    exL( fov"B" )
    allL( "Ant_2", le"(g B)" )
    exL( fov"A" )
    exR( fov"B" )
    unfold( "Ech" ) atMost 1 in "Suc_0_0"
    exR( "Suc_0_0", fov"A" )
    andL( "Ant_2_1" )
    andL
    andR
    andR
    ref( "nu" )
    foTheory
    foTheory

  }
  val mubaseBc = Lemma( esMubaseBc ) {
    allL( "Ant_2", hoc"z:i" )
    exL( fov"B" )
    allL( "Ant_2", le"(g B)" )
    exL( fov"A" )
    exR( fov"B" )
    unfold( "Ech" ) atMost 1 in "Suc_0_0"
    exR( "Suc_0_0", fov"A" )
    andL( "Ant_2_1" )
    andL
    andR
    foTheory
    foTheory
  }
  val mubaseSc = Lemma( esMubaseSc ) {
    allL( "Ant_2", hoc"z:i" )
    exL( fov"B" )
    allL( "Ant_2", le"(g B)" )
    exL( fov"A" )
    exR( fov"B" )
    unfold( "Ech" ) atMost 1 in "Suc_0_0"
    exR( "Suc_0_0", fov"A" )
    andL( "Ant_2_1" )
    andL
    andR
    andR
    ref( "nu" )
    foTheory
    foTheory
  }
  val chiBc = Lemma( esChiBc ) {
    unfold( "POR" ) atMost 1 in "Suc_0"
    unfold( "POR" ) atMost 1 in "Ant_2"
    trivial
  }
  val chiSc = Lemma( esChiSc ) {
    unfold( "POR" ) atMost 1 in "Suc_0"
    unfold( "POR" ) atMost 1 in "Ant_2"
    orR
    orL
    trivial
    ref( "chi" )
  }
  val phiBc = Lemma( esphiBc ) {
    allL( "Ant_2", hoc"z:i" )
    exL( fov"B" )
    allL( "Ant_2", le"(g B)" )
    exL( fov"A" )
    exR( fov"A" )
    andL( "Ant_2_1" )
    unfold( "POR" ) atMost 1 in "Ant_2_1_1"
    ref( "nuPrime" )
  }
  val esphiSc = Sequent(
    Seq(
      "Ant_2" -> hof"!x?y (LEQ(x,y) & POR(s(n),y))" ),
    Seq( "Suc_0" -> hof"?p Ech(m,p)" ) )
  val phiSc = Lemma( esphiSc ) {
    cut( "cut", hof"!x?y (LEQ(x,y) & E(f(y),s(n)))" )
    cut( "cut1", hof"!x?y (LEQ(x,y) & POR(n,y))" )
    allR( "cut", fov"B" )
    allR( "cut1", fov"A" )
    allL( "Ant_2", le"max(A,B)" )
    exL( "Ant_2_0", fov"C" )
    exR( "cut", fov"C" )
    exR( "cut1", fov"C" )
    andL
    andR( "cut_0" )
    andR( "cut1_0" )
    foTheory
    foTheory
    unfold( "POR" ) atMost 1 in "Ant_2_0_1"
    orL
    trivial
    andR( "cut1_0" )
    foTheory
    forget( "Ant_2_0_0" )
    forget( "Ant_2" )
    forget( "Suc_0" )
    forget( "cut" )
    forget( "cut1" )
    forget( "cut_0" )
    ref( "chi" )
    focus( 1 )
    ref( "mu" )
    ref( "phi" )
  }
  val omegaBc = Lemma( esOmegaBc ) {
    cut( "cut", hof"!x?y (LEQ(x,y) & E(f(y),0))" )
    allR( fov"A" )
    allL( "Ant_2", fov"A" )
    exR( "cut", fov"A" )
    unfold( "POR" ) atMost 1 in "Ant_2_0"
    andR
    foTheory
    trivial
    ref( "mubase" )
  }
  val omegaSc = Lemma( esOmegaSc ) {
    cut( "cut", hof"!x?y (LEQ(x,y) & POR(s(n),y))" )
    allR( fov"A" )
    allL( "Ant_2", fov"A" )
    exR( "cut", fov"A" )
    andR
    foTheory
    ref( "chi" )
    ref( "phi" )
  }

//Notice that the inactive parameter does not have an sucessor function
//around it but the active one does. Also the active parameter is always 
//the first one
  ctx += Context.ProofDefinitionDeclaration( le"nu 0 n A", NuBc )
//m is active and n is not
  ctx += Context.ProofDefinitionDeclaration( le"nu (s m) n  A", NuSc )
  ctx += Context.ProofDefinitionDeclaration( le"nuPrime 0 A", NuPrimeBc )
  ctx += Context.ProofDefinitionDeclaration( le"nuPrime (s m) A", NuPrimeSc )
  ctx += Context.ProofDefinitionDeclaration( le"mu 0 n", muBc )
  ctx += Context.ProofDefinitionDeclaration( le"mu (s m) n ", muSc )
  ctx += Context.ProofDefinitionDeclaration( le"mubase 0", mubaseBc )
  ctx += Context.ProofDefinitionDeclaration( le"mubase (s m)", mubaseSc )
  ctx += Context.ProofDefinitionDeclaration( le"chi 0 a", chiBc )
  ctx += Context.ProofDefinitionDeclaration( le"chi (s n) a", chiSc )
  ctx += Context.ProofDefinitionDeclaration( le"phi 0 m", phiBc )
//n is active m is not
  ctx += Context.ProofDefinitionDeclaration( le"phi (s n) m", phiSc )
  ctx += Context.ProofDefinitionDeclaration( le"omega 0 m", omegaBc )
  ctx += Context.ProofDefinitionDeclaration( le"omega (s n) m", omegaSc )


//We can now perform the same steps as in the previous file but we two parameters
//to substitute

val FullProof = instantiateProof.Instantiate(le"omega (s (s (s (s 0)))) (s (s (s (s (s (s 0))))))") 
val thestruct = StructCreators.extract( FullProof )
val cs = CharacteristicClauseSet( thestruct )



}


