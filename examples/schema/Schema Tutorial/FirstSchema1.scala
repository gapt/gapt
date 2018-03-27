package gapt.examples

import gapt.expr._
import gapt.proofs.Context._
import gapt.proofs.gaptic._
import gapt.proofs.Context
import gapt.proofs.Sequent

object FirstSchema1 extends TacticsProof {
  //These are the two fundamental additions to the context needed for Schematic
  //proof construction.
  ctx += Context.InductiveType( "nat", hoc"0 : nat", hoc"s : nat>nat" ) //defines the natural numbers
  ctx += Context.Sort( "i" ) //defines the first order term sort

  // Note that at this point both sorts are empty (though in the case of the type "nat"
  // we do have the individuals 0, s(0), s(s(0)), and so on, but no predicates or
  //additional function symbols). We need to add constants, functions,
  // and predicate symbols individually to the sorts. The above declarations
  // only provide the particular types this objects can have but not the
  // individuals of these types.

  // Let us consider the "i" as a numeric sort but with different symbolism than the
  // sort "nat" which will represent true natural numbers.

  ctx += hoc"z:i" //This is the Zero for the "i" sort
  ctx += hoc"g:i>i" //This is the Successor for the "i" sort

  // the hoc prefix on the two strings tells us that these are higher-order constants
  // the type of these constants is represented by the :i and :i>i . As one can guess
  // z is a constant and  g is a function constant taking one argument. We can also
  // make a function constant which uses both of the introduced sorts.

  ctx += hoc"f:i>nat" //Takes a term of "i" and returns a term of "nat"

  //in FirstSchema2.scala we continue with the introduction of predicates, theory
  // axioms, proof names, and primitive recursive symbols.

}
