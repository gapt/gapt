


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





object cyclicExample extends TacticsProof {

  // Type
  ctx += InductiveType("nat", hoc"0 : nat", hoc"s : nat>nat")
  ctx += Sort("i")

  // Term Constants
  //ctx += hoc"z:i"
  //ctx += hoc"g:i>i"
  //ctx += hoc"f:i>nat"
  //ctx += hoc"max:i>i>i"

  // Predicate Constants
  //ctx += hoc"Add1: nat>nat>nat>o"
  //ctx += hoc"Add2: nat>nat>nat>o"
  

  // Theory Axioms
  //ctx += "Add1Ax" -> hos"E(f(p),n),E(f(q),n) :- E(f(p),f(q))"

  //ctx += "Add1 x y z" -> hof"(( x = 0  ∧ z = y ) ∨ (?x' ?y' x = s(x') ∧ z = s(z') ∧ Add1(x',y,')))"//Adding a definition  
  ctx += hof" Add1 x y z = (( x = 0  ∧ z = y ) ∨ (?(u:nat) ?(v:nat) (x = s(u) ∧ z = s(v) ∧ Add1(u,y,v) ) ))" //Adding a definition as an equation
//∧ Add1(x',y,z')

// TODO: Add this as rec func

  // Proof names
  ctx += hoc"d1: nat>nat"


  // Proof End Sequent
  val esD1 = Sequent(Seq(), Seq(hof"!y !z (Add1(n,s(y),z) -> Add1(s(n),y,z))"))

  // Proof Declarations
  ctx += ProofNameDeclaration(le"d1 n", esD1)
 
  // basecase and stepcase  end sequents
  val esD1Bc = Sequent(Seq(), Seq("Suc_0" -> hof"!y !z (Add1(0,s(y),z) -> Add1(s(0),y,z))" ))
  val esD1Sc = Sequent(Seq(), Seq("Suc_0" -> hof"!y !z (Add1(s(n),s(y),z) -> Add1(s(s(n)),y,z))"))

    // Proof of chi basecase
  val D1Bc = Lemma(esD1Bc) {
    allR("Suc_0")
    //allR("Suc_0")
    //impR
  }



}