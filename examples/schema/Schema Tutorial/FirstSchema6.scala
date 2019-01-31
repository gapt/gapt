package gapt.examples

import gapt.expr._
import gapt.proofs.gaptic._
import gapt.proofs.Sequent
import gapt.proofs.context.Context
import gapt.proofs.context.update.InductiveType
import gapt.proofs.context.update.{ PrimitiveRecursiveFunction => PrimRecFun }
import gapt.proofs.context.update.ProofDefinitionDeclaration
import gapt.proofs.context.update.ProofNameDeclaration
import gapt.proofs.context.update.Sort
import gapt.proofs.lk.util.instantiateProof
//used to unfold proof schema

object FirstSchema6 extends TacticsProof {
  //Type
  ctx += InductiveType( "nat", hoc"0 : nat", hoc"s : nat>nat" )
  ctx += Sort( "i" )
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
  val esOmega = Sequent( Seq( hof"!x POR(n,x)" ), Seq( hof"?p?q (LE(p,q) & E(f(p),f(q)))" ) )
  val esphi = Sequent( Seq( hof"!x?y (LEQ(x,y) & POR(n,y) )" ), Seq( hof"?p?q (LE(p,q) & E(f(p),f(q)))" ) )
  val eschi = Sequent( Seq( hof" POR(n,a) " ), Seq( hof"POR(n,a)" ) )
  //Proof Declarations
  ctx += ProofNameDeclaration( le"omega n", esOmega )
  ctx += ProofNameDeclaration( le"phi n", esphi )
  ctx += ProofNameDeclaration( le"chi n a", eschi )
  //basecase and stepcase  end sequents
  val esChiBc = Sequent( Seq( "Ant_0" -> hof" POR(0,a)" ), Seq( "Suc_0" -> hof"POR(0,a)" ) )
  val esChiSc = Sequent( Seq( "Ant_0" -> hof" POR(s(n),a)" ), Seq( "Suc_0" -> hof"POR(s(n),a)" ) )
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
    ref( "chi" ) // The proof link tactic
  }
  //Proof definitions
  ctx += ProofDefinitionDeclaration( le"chi 0 a", chiBc )
  //Notice that like the base case the proof definition includes the fact that we
  //are defining the step case
  ctx += ProofDefinitionDeclaration( le"chi (s n) a", chiSc )

  //now if we run the command prooftool(FirstSchema.chiSc) we get a proof with a link to itself
  //and thus we have our first schema proof although a quite silly one.

  //We can instantiate the proof schema of chi as follows:

  val chiThree = instantiateProof( le"chi (s (s (s (s (s (s 0)))))) a" )

  //Now run prooftool(FirstSchema.chiThree)

  //In some sense most of what we have done so far is not really proof schema specific.
  //we haven't really used the various parts of the context to the fulliest extent. Now
  // move on to FirstSchema7.scala

}
