package gapt.examples

import gapt.expr._
import gapt.proofs.Context._
import gapt.proofs.gaptic._
import gapt.proofs.Context
import gapt.proofs.Sequent

object FirstSchema5 extends TacticsProof {
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
  val esOmega = Sequent( Seq( hof"!x POR(n,x)" ), Seq( hof"?p?q (LE(p,q) & E(f(p),f(q)))" ) )
  val esphi = Sequent( Seq( hof"!x?y (LEQ(x,y) & POR(n,y) )" ), Seq( hof"?p?q (LE(p,q) & E(f(p),f(q)))" ) )
  val eschi = Sequent( Seq( hof" POR(n,a) " ), Seq( hof"POR(n,a)" ) )
  //Proof Declarations
  ctx += Context.ProofNameDeclaration( le"omega n", esOmega )
  ctx += Context.ProofNameDeclaration( le"phi n", esphi )
  ctx += Context.ProofNameDeclaration( le"chi n a", eschi )
  //Chi basecase end sequent
  val esChiBc = Sequent( Seq( "Ant_0" -> hof" POR(0,a)" ), Seq( "Suc_0" -> hof"POR(0,a)" ) )
  //Proof of chi basecase
  val chiBc = Lemma( esChiBc ) {
    unfold( "POR" ) atMost 1 in "Suc_0"
    unfold( "POR" ) atMost 1 in "Ant_0"
    trivial
  }
  //If, after loading the file, we run  FirstSchema.chiBc we should get a proof.
  /*
gapt> FirstSchema.chiBc
res1: gapt.proofs.lk.LKProof =
[p3] POR(0:nat, #v(a: i)) ⊢ POR(0, #v(a: i))    (DefinitionRightRule(p2, Suc(0), POR(0:nat, #v(a: i)): o))
[p2] POR(0:nat, #v(a: i)) ⊢ E(f(#v(a: i)): nat, 0)    (DefinitionLeftRule(p1, Ant(0), POR(0:nat, #v(a: i)): o))
[p1] E(f(#v(a: i)): nat, 0:nat) ⊢ E(f(#v(a: i)), 0)    (LogicalAxiom(E(f(#v(a: i)): nat, 0:nat): o))
*/

  //We can open this proof in prooftool by typing prooftool(FirstSchema.chiBc). The last step is to add this
  //proof to the context to the ProofDefinition facet using the following command.
  ctx += Context.ProofDefinitionDeclaration( le"chi 0 a", chiBc )

  //This is similar to a proof declaration except the variables are instantiated correctly to associate with
  //the specific case addressed.

  //Now we need to build the step case of chi in a similar fashion.

  val esChiSc = Sequent( Seq( "Ant_0" -> hof" POR(s(n),a)" ), Seq( "Suc_0" -> hof"POR(s(n),a)" ) )

  //Notice two differences between esChiSc and esChiBc, not only are both n and a present but we have also
  //add a sucessor symbol around n. This tells the system that this is a stepcase sequent. This must
  //always be added, even in the case of multiple parameters, though it is a bit more complex and will
  //be addressed later.

  val chiSc = Lemma( esChiSc ) {
    unfold( "POR" ) atMost 1 in "Suc_0"
    unfold( "POR" ) atMost 1 in "Ant_0"
    orR
    orL
  }

  //Now load the file and run the command FirstSchema.chiSc. What you might notice is that you get a similar
  //output as before, but this time we have more open goals because orL generates two branches. Also context is duplicated.

  /*
gapt.proofs.gaptic.QedFailureException: Proof not completed. There are still 2 open sub goals:
Ant_0: E(f(a), s(n))
:-
Suc_0_0: E(f(a), s(n))
Suc_0_1: POR(n, a)

Ant_0: POR(n, a)
:-
Suc_0_0: E(f(a), s(n))
Suc_0_1: POR(n, a)

  at gapt.proofs.gaptic.LemmaMacros$.finish(language.scala:45)
  at gapt.proofs.gaptic.LemmaMacros$.finishLemma(language.scala:55)
  ... 28 elided

*/

  //however, even though context is duplicated it is ignored by the trivial rule, but that leaves another problem, the
  // second open goal is not trivial. How do we close the proof. See FirstSchema6.scala
}
