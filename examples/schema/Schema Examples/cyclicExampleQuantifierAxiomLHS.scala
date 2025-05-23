


import gapt.expr._
import gapt.proofs.gaptic._
import gapt.proofs.Sequent
import gapt.proofs.ceres.CharacteristicClauseSet
import gapt.proofs.ceres.StructCreators
import gapt.proofs.context.Context
import gapt.proofs.context.update.InductiveType
import gapt.proofs.context.update.{PrimitiveRecursiveFunction => PrimRecFun}
import gapt.proofs.context.update.ProofDefinitionDeclaration
import gapt.proofs.context.update.ProofNameDeclaration
import gapt.proofs.context.update.Sort
import gapt.proofs.lk.util.instantiateProof
import gapt.proofs.lk.transformations.cutNormal





object cyclicExampleQuantifierAxiomLHS extends TacticsProof {

  // Type
  ctx += InductiveType("nat", hoc"0 : nat", hoc"s : nat>nat")
  ctx += Sort("i")

  // Theory Axioms
  //ctx += "A2" -> hos" (s(p)= s(q) ) -> (p = q) "  // Check if we want to have it like this
  


  // Primitive Recursive Definitions
  ctx += PrimRecFun(hoc"Add1:nat>nat>nat>o", 
                       "Add1 0 y z          = ( z = y )", // Base Case
                       "Add1 (s(x:nat)) y z = (?(u:nat) ?(v:nat) (s(x) = s(u) ∧ z = s(v) ∧ Add1(u,y,v) ) )" ) // Step Case

  ctx += PrimRecFun(hoc"Add2:nat>nat>nat>o", 
                       "Add2 0 y z          = ( z = y )", // Base Case
                       "Add2 (s(x:nat)) y z = (?(u:nat)  (s(x) = s(u) ∧ Add2(u,s(y),z) ) )" ) // Step Case

  // Proof names
  ctx += hoc"d1: nat>nat>nat>nat"
  ctx += hoc"phi: nat>nat"
  


  // Proof End Sequent
  val esD1 = Sequent(Seq(hof"!p !q ((s(p)= s(q) ) -> (p = q)) " ), Seq(hof"!y !z (Add1(n,s(y),z) -> Add1(s(n),y,z))"))
  //val esD1 = Sequent(Seq(), Seq(hof"Add1(n,s(y),z) -> Add1(s(n),y,z)"))
  val esPhi = Sequent(Seq(hof"!p !q ((s(p)= s(q) ) -> (p = q)) "), Seq(hof"!y !z (Add2(n,y,z) -> Add1(n,y,z))"))

  // Proof Declarations
  ctx += ProofNameDeclaration(le"d1 n ", esD1)
  //ctx += ProofNameDeclaration(le"d1 n y z", esD1)
  ctx += ProofNameDeclaration(le"phi n", esPhi)
 
  // basecase and stepcase  end sequents
  val esD1Bc = Sequent(Seq("A2Ax" -> hof"!p !q ((s(p)= s(q) ) -> (p = q)) "), Seq("Suc_0" -> hof"!y !z (Add1(0,s(y),z) -> Add1(s(0),y,z))" ))
  val esD1Sc = Sequent(Seq("A2Ax" -> hof" !p !q ((s(p)= s(q) ) -> (p = q)) "), Seq("Suc_0" -> hof"!y !z (Add1(s(n),s(y),z) -> Add1(s(s(n)),y,z))"))
  //val esD1Bc = Sequent(Seq(), Seq("Suc_0" -> hof"Add1(0,s(y),z) -> Add1(s(0),y,z)" ))
  //val esD1Sc = Sequent(Seq(), Seq("Suc_0" -> hof"Add1(s(n),s(y),z) -> Add1(s(s(n)),y,z)"))

  val esPhiBc = Sequent(Seq("A2Ax" -> hof"!p !q ((s(p)= s(q) ) -> (p = q)) "), Seq("Suc_0" -> hof"!y !z (Add2(0,y,z) -> Add1(0,y,z))" ))
  val esPhiSc = Sequent(Seq("A2Ax" -> hof"!p !q ((s(p)= s(q) ) -> (p = q)) "), Seq("Suc_0" -> hof"!y !z (Add2(s(n),y,z) -> Add1(s(n),y,z))"))

    // Proof of D1 basecase
  val D1Bc = Lemma(esD1Bc) {
    forget("A2Ax")
    allR("Suc_0")
    allR("Suc_0")
    impR
    unfold("Add1") atMost 1 in "Suc_0_0"
    unfold("Add1") atMost 1 in "Suc_0_1"
    exR("Suc_0_1", hoc"0")
    exR("Suc_0_1_0",hov"y:nat")
    forget("Suc_0_1")
    forget("Suc_0_1_0")
    andR
    andR

   
    trivial
    trivial
    unfold("Add1") atMost 1 in "Suc_0_1_0_0"
    forget("Suc_0_0")
    trivial

    
  }


  
  val D1Sc = Lemma(esD1Sc) {
    cut("cut", hof"!y !z (Add1(n, s(y), z) -> Add1(s(n),y,z) )")

    forget("Suc_0")
    ref("d1")

    allR("Suc_0")
    allR("Suc_0")
    impR
    unfold("Add1") atMost 1 in "Suc_0_0"
    exL("Suc_0_0")
    exL("Suc_0_0")
    andL
    andL
    
    unfold("Add1") atMost 1 in "Suc_0_1"

    
    exR("Suc_0_1",le"s(n)")
    exR("Suc_0_1_0",le"v:nat") // <- maybe here s(v)
    forget("Suc_0_1")
    forget("Suc_0_1_0")
   // eql("Suc_0_0_0_1", "cut")
  
    
     andR
     andR
    trivial
    trivial

    forget("Suc_0_0_0_1") // brauchen wir vl. noch
    allL("cut",le"y:nat")
    allL("cut_0",le"v:nat")
    forget("cut")
    forget("cut_0")

    allL("A2Ax",le"n:nat")
    allL("A2Ax_0",le"u:nat")

    forget("A2Ax")
    forget("A2Ax_0")
    impL("A2Ax_0_0")

    trivial
   

    forget("Suc_0_0_0_0")
    eql("A2Ax_0_0", "Suc_0_0_1")
    forget("A2Ax_0_0")
    impL
    trivial
    trivial

    
    
}




  ctx += ProofDefinitionDeclaration(le"d1 0", D1Bc) 
  ctx += ProofDefinitionDeclaration(le"d1 (s n)", D1Sc)

  // Instantiation
  val d1Zero = instantiateProof(le"d1 0")
  val d1One = instantiateProof(le"d1 (s 0)")
  val d1Two = instantiateProof(le"d1 (s (s 0))")
  val d1Three = instantiateProof(le"d1 (s (s (s 0)))")

  val thestruct = StructCreators.extract(d1One)
  val cs = CharacteristicClauseSet(thestruct)


//////////////////////////
// Full proof
//////////////////////////

  
  val phiBc = Lemma(esPhiBc) {
    forget("A2Ax")
    allR("Suc_0")
    allR("Suc_0")
    impR
    unfold("Add2") atMost 1 in "Suc_0_0"
    unfold("Add1") atMost 1 in "Suc_0_1"
    trivial
  }



  val phiSc = Lemma(esPhiSc) {
   cut("cut", hof"!y !z (Add2(n, y, z) -> Add1(n,y,z) )")
   forget("Suc_0")
   ref("phi") // add again

   allR("Suc_0")
   allR("Suc_0")
   impR
   unfold("Add2") atMost 1 in "Suc_0_0"
   exL("Suc_0_0")
   andL



    allL("A2Ax",le"n:nat")
    allL("A2Ax_0",le"u:nat")

  //  forget("A2Ax")
    forget("A2Ax_0")
    impL("A2Ax_0_0")
    trivial



   forget("Suc_0_0_0")
   eql("A2Ax_0_0", "Suc_0_0_1")
   forget("A2Ax_0_0")

   allL("cut",le"s(y):nat")
   allL("cut_0",le"z:nat")

   forget("cut")
   forget("cut_0")

   impL
   trivial
   forget("Suc_0_0_1")

   cut("cutLink", hof"!y !z (Add1(n,s(y),z) -> Add1(s(n),y,z))")
   forget("cut_0_0")
   forget("Suc_0_1")
   //theory
   ref("d1") // add later

   allL("cutLink", le"y:nat")
   allL("cutLink_0", le"z:nat")
   forget("cutLink")
   forget("cutLink_0")
   impL
   trivial
   trivial

   
  }

  ctx += ProofDefinitionDeclaration(le"phi 0", phiBc) 
  ctx += ProofDefinitionDeclaration(le"phi (s n)", phiSc)

  val FullProof0 = instantiateProof(le"phi 0")

  val FullProof1 = instantiateProof(le"phi (s 0)")
  val thestruct1 = StructCreators.extract(FullProof1)
  val cs1 = CharacteristicClauseSet(thestruct1)
  val redCut1 = cutNormal( FullProof1 )

  val FullProof2 = instantiateProof(le"phi (s (s 0))")
  val thestruct2 = StructCreators.extract(FullProof2)
  val cs2 = CharacteristicClauseSet(thestruct2)
  val redCut2 = cutNormal( FullProof2 )

  val FullProof3 = instantiateProof(le"phi (s (s (s 0)))")
  val thestruct3 = StructCreators.extract(FullProof3)
  val cs3 = CharacteristicClauseSet(thestruct3)
  val redCut3 = cutNormal( FullProof3 )

  val FullProof6 = instantiateProof(le"phi (s (s (s (s (s (s 0))))))")
  val thestruct6 = StructCreators.extract(FullProof6)
  val cs6 = CharacteristicClauseSet(thestruct6)
  val redCut6 = cutNormal( FullProof6 )

  


  // Run to see the clause set in prooftool
  // prooftool(cs)


}