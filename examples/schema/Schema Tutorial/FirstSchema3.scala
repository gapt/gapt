package gapt.examples

import gapt.expr._
import gapt.proofs.Sequent
import gapt.proofs.context.update.InductiveType
import gapt.proofs.context.update.{PrimitiveRecursiveFunction => PrimRecFun}
import gapt.proofs.context.update.ProofNameDeclaration
import gapt.proofs.context.update.Sort
import gapt.proofs.gaptic._

object FirstSchema3 extends TacticsProof {
  // Type
  ctx += InductiveType("nat", hoc"0 : nat", hoc"s : nat>nat")
  ctx += Sort("i")
  // Term Constants
  ctx += hoc"z:i"
  ctx += hoc"g:i>i"
  ctx += hoc"f:i>nat"
  ctx += hoc"max:i>i>i"
  // Predicate Constants
  ctx += hoc"E: nat>nat>o"
  ctx += hoc"LEQ: i>i>o"
  ctx += hoc"LE: i>i>o"
  // Theory Axioms
  ctx += "efef" -> hos"E(f(p),n),E(f(q),n) :- E(f(p),f(q))"
  ctx += "leq_refl" -> hos" :- LEQ(p,p)"
  ctx += "leq_g" -> hos"LEQ(g(p),q):- LE(p,q)"
  ctx += "leq_max1" -> hos"LEQ(max(a, b), c) :- LEQ(a, c)"
  ctx += "leq_max2" -> hos"LEQ(max(a, b), c) :- LEQ(b, c)"
  // Proof Names
  ctx += hoc"omega: nat>nat"
  ctx += hoc"phi: nat>nat"
  ctx += hoc"chi: nat>i>nat"
  // Primitive Recursive Definitions
  ctx += PrimRecFun(hoc"POR:nat>i>o", "POR 0 x = E (f x) 0", "POR (s y) x = (E (f x) (s y) ∨ POR y x)")

  // The names are there to match proofs to the appropiate end sequents. This is done
  // using the ProofNameDeclaration Facet of the context. But first we need to construct
  // the end sequents which are associated with each proof name

  val esOmega = Sequent(Seq(hof"!x POR(n,x)"), Seq(hof"?p?q (LE(p,q) & E(f(p),f(q)))"))
  val esphi = Sequent(Seq(hof"!x?y (LEQ(x,y) & POR(n,y) )"), Seq(hof"?p?q (LE(p,q) & E(f(p),f(q)))"))
  val eschi = Sequent(Seq(hof" POR(n,a) "), Seq(hof"POR(n,a)"))

  // a sequent is a pair of sequences. The first sequence is the antecedent and the second is the succedent.
  // If one wants more than one formula in the sequences one just needs to add a comma between each formula.
  // notice that each formula is prefixed by hof or higher order function, this concerns the interpretation of
  // quantifiers as lambda expressions.

  // Now that we have the end sequents we need to add the association to the context. The important thing is
  // that all the free variables in the sequents are present in the association. For example eschi has two
  // free variable thus, its association expression must have two free variables.

  ctx += ProofNameDeclaration(le"omega n", esOmega)
  ctx += ProofNameDeclaration(le"phi n", esphi)
  ctx += ProofNameDeclaration(le"chi n a", eschi)

  // The above code presents how one can add the association between the proof name, free variables, and end
  // sequent. Note that once again we are using application form for the expression,
  // i.e. chi n a and not chi(n,a).

  // Now we can finally start constructing proofs. See FirstSchema4.scala

}
