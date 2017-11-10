import at.logic.gapt.expr._  
import at.logic.gapt.proofs.Context._ 
import at.logic.gapt.proofs.gaptic._ 
import at.logic.gapt.proofs.Context  
import at.logic.gapt.proofs.Sequent  

object FirstSchema extends TacticsProof {
//Type
ctx += Context.InductiveType( "nat", hoc"0 : nat", hoc"s : nat>nat" )
ctx += Context.Sort( "i" )
//Term Constants
ctx += hoc"z:i"
ctx += hoc"g:i>i"
ctx += hoc"f:i>nat"
ctx += hoc"max:i>i>i"
//Predicate Constants
ctx += hoc"E: nat>nat>o" 
ctx += hoc"LEQ: i>i>o"   
ctx += hoc"LE: i>i>o"
//Theory Axioms
ctx += "efef" -> hos"E(f(p),n),E(f(q),n) :- E(f(p),f(q))"
ctx += "leq_refl" -> hos" :- LEQ(p,p)"
ctx += "leq_g" -> hos"LEQ(g(p),q):- LE(p,q)"
ctx += "leq_max1" -> hos"LEQ(max(a, b), c) :- LEQ(a, c)"
ctx += "leq_max2" -> hos"LEQ(max(a, b), c) :- LEQ(b, c)"
//Proof Names
ctx += hoc"omega: nat>nat"
ctx += hoc"phi: nat>nat"
ctx += hoc"chi: nat>i>nat"
//Primitive Recursive Definitions
ctx += PrimRecFun( hoc"POR:nat>i>o", "POR 0 x = E (f x) 0", "POR (s y) x = (E (f x) (s y) ∨ POR y x)" )
//Proof End Sequent
val esOmega = Sequent(Seq( hof"!x POR(n,x)" ),Seq( hof"?p?q (LE(p,q) & E(f(p),f(q)))" ) )
val esphi   = Sequent(Seq( hof"!x?y (LEQ(x,y) & POR(n,y) )" ),Seq( hof"?p?q (LE(p,q) & E(f(p),f(q)))" ) )
val eschi   = Sequent(Seq( hof" POR(n,a) " ),Seq( hof"POR(n,a)" ) )
//Proof Declarations
ctx += Context.ProofNameDeclaration( le"omega n", esOmega )
ctx += Context.ProofNameDeclaration( le"phi n", esphi )
ctx += Context.ProofNameDeclaration( le"chi n a", eschi )
//basecase and stepcase  end sequents
val esChiBc = Sequent(Seq("Ant_0" -> hof" POR(0,a)" ),Seq("Suc_0" -> hof"POR(0,a)" ) )
val esChiSc = Sequent(Seq("Ant_0" -> hof" POR(s(n),a)" ), Seq("Suc_0" -> hof"POR(s(n),a)" ) )
val esphiBc = Sequent(Seq("Ant_0" -> hof"!x?y (LEQ(x,y) & POR(0,y))" ),Seq( "Suc_0" -> hof"?p?q (LE(p,q) & E(f(p),f(q))) " ) )
val esphiSc = Sequent(Seq("Ant_0" -> hof"!x?y (LEQ(x,y) & POR(s(n),y))" ),Seq( "Suc_0" -> hof"?p?q (LE(p,q) & E(f(p),f(q)))" ) )
  val esOmegaBc = Sequent(Seq( "Ant_2" -> hof"!x POR(0,x)" ),Seq( "Suc_0" -> hof"?p?q (LE(p,q) & E(f(p),f(q))) " ) )
val esOmegaSc = Sequent(Seq( "Ant_2" -> hof"!x POR(s(n),x)" ),Seq( "Suc_0" -> hof"?p?q (LE(p,q) & E(f(p),f(q))) " ) )
//Proof of chi basecase
  val chiBc = Lemma( esChiBc ) {
    unfold( "POR" ) atMost 1 in "Suc_0"
    unfold( "POR" ) atMost 1 in "Ant_0"
    trivial
}
//Proof of chi Stepcase
 val chiSc = Lemma( esChiSc ) {
    unfold( "POR" ) atMost 1 in "Suc_0"
    unfold( "POR" ) atMost 1 in "Ant_0"
    orR
    orL
    trivial
    ref("chi") 
  }
 //The base case of phi
  val phiBc = Lemma( esphiBc ) {
    allL( "Ant_0", hoc"z:i" )
    exL( fov"B" )
    allL( "Ant_0", le"(g B)" )
    exL( fov"A" )
    exR( fov"B" )
    forget( "Suc_0" )
    exR( fov"A" )
    forget( "Suc_0_0" )
    andL( "Ant_0_1" )
    andL
    andR
    foTheory
    unfold( "POR" ) atMost 1 in "Ant_0_0_1"
    unfold( "POR" ) atMost 1 in "Ant_0_1_1"
    foTheory
  }
  //The step case of phi
  val phiSc = Lemma( esphiSc ) {
    cut( "cut", hof"!x?y (LEQ(x,y) & E(f(y),s(n)))" )
    cut( "cut1", hof"!x?y (LEQ(x,y) & POR(n,y))" )
    allR( "cut", fov"B" )
    allR( "cut1", fov"A" )
    allL( "Ant_0", le"max(A,B)" )
    exL( "Ant_0_0", fov"C" )
    exR( "cut", fov"C" )
    exR( "cut1", fov"C" )
    andL
    andR( "cut_0" )
    andR( "cut1_0" )
    foTheory
    foTheory
    unfold( "POR" ) atMost 1 in "Ant_0_0_1"
    orL
    trivial
    andR( "cut1_0" )
    foTheory
    forget( "Ant_0_0_0" )
    forget( "Ant_0" )
    forget( "Suc_0" )
    forget( "cut" )
    forget( "cut1" )
    forget( "cut_0" )
    ref( "chi" )
    focus( 1 )         
    forget( "Ant_0" )  
    allL( hoc"z:i" )
    exL( fov"B" )
    allL( le"(g B)" )
    exL( fov"A" )
    exR( fov"B" )
    forget( "Suc_0" )
    exR( fov"A" )
    forget( "Suc_0_0" )
    andL( "cut_1" )
    andL
    andR
    foTheory
    foTheory       
    ref( "phi" ) 
  }

//omega step case proof
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
//omega base case proof
  val omegaBc = Lemma( esOmegaBc ) {
    cut( "cut", hof"!x?y (LEQ(x,y) & E(f(y),0))" )
    allR( fov"A" )
    allL( "Ant_2", fov"A" )
    exR( "cut", fov"A" )
    unfold( "POR" ) atMost 1 in "Ant_2_0"
    andR
    foTheory
    trivial
    forget( "Ant_2" )
    allL( hoc"z:i" )
    exL( fov"B" )
    allL( le"(g B)" )
    exL( fov"A" )
    exR( fov"B" )
    forget( "Suc_0" )
    exR( fov"A" )
    forget( "Suc_0_0" )
    andL( "cut_1" )
    andL
    andR
    foTheory
    foTheory
  }
//Proof definitions
ctx += Context.ProofDefinitionDeclaration( le"chi 0 a", chiBc )
ctx += Context.ProofDefinitionDeclaration( le"chi (s n) a", chiSc )
ctx += Context.ProofDefinitionDeclaration( le"phi 0", phiBc )
ctx += Context.ProofDefinitionDeclaration( le"phi (s n)", phiSc )
ctx += Context.ProofDefinitionDeclaration( le"omega 0", omegaBc )
ctx += Context.ProofDefinitionDeclaration( le"omega (s n)", omegaSc )


//Now we show how one can compare the two extracted clause sets for the full proof

val FullProof = instantiateProof.Instantiate( le"omega (s (s (s (s (s (s 0))))))" ) 
val thestruct = StructCreators.extract( FullProof )
//Notice that we need to apply subsumption removal to get rid of some of the useless clauses
val cs = CharacteristicClauseSet( thestruct )
//Run to see the clause set in prooftool
//prooftool(cs)

//The next step is dealing with multiple parameters at once. FirstSchemaFile_9.Scala


}
