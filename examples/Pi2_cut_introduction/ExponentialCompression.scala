package gapt.examples

import gapt.expr._
import gapt.proofs.Context._
import gapt.proofs.gaptic._
import gapt.proofs.Context
import gapt.proofs.Sequent

object ExponentialCompression extends TacticsProof {
  ctx += Context.InductiveType( "nat", hoc"0 : nat", hoc"s : nat>nat" )
  ctx += Context.Sort( "i" )

  ctx += hoc"a:i"
  ctx += hoc"f:i>i"
  ctx += hoc"g:i>i"
  ctx += hoc"fn:nat>i>i"

  ctx += hoc"P: i>i>o"
  ctx += hoc"Disjunction: nat>i>o"
  ctx += hoc"Conjunction: nat>i>i>o"

  ctx += "Endsequent" -> hos"!x (Disjunction(n,x)) , !y!z (Conjunction(n,y,z) => P(y,g(z))) , !x!y (P(x,y) => P(x,f(y))) :- ?x?y (P(x,g(y)))"

  ctx += hoc"omega: nat>nat"
  ctx += hoc"phi: nat>nat"
  ctx += hoc"chi: nat>i>nat"

  //Proof names always end with a type "nat". The arguements before the final nat represents
  // the arguements associated with the proof name. That is omega takes one arguement while
  // chi takes two.

  //The only thing missing for the construction of proof schema are primitive recursive definitions
  //of functions and predicates.

  ctx += PrimRecFun( hoc"POR:nat>i>o", "POR 0 x = E (f x) 0", "POR (s y) x = (E (f x) (s y) ∨ POR y x)" )

  //Notice that this uses a different syntax than our previous context extensions, that is we write
  //functions and predicates as applications, i.e. E (f x) 0 instead of E(f(x),0). This is
  // important to note or you will get frustrated when it does not work. The first arguement is
  //the name and type of the predicate (or function). in this case "POR:nat>i>o" or Primitive
  //recursive OR. The second arguement is the basecase and the thirds is the step case.

  //In FirstSchema3.scala we go over the schema specific parts of the Context

}