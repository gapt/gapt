package gapt.examples
import gapt.expr._ //Used to construct terms
import gapt.proofs.Context._ //Provides access to various parts of the context
import gapt.proofs.gaptic._ //The tactics language used for constructing proofs
import gapt.proofs.Context //The actual context object
import gapt.proofs.Sequent // needed for constructing sequents

object FirstSchema0 extends TacticsProof {

  //This is where the actual proof is constructed and stored.
  //calling this object will result in the construction of the
  //proof or proof schema.

  /* More about the context */
  //Everything is stored within the context, the proof components, proof names, end sequents
  //of proofs, recursive predicates, logical sorts, and theory axioms.
  // See FirstSchema0.scala for more details.

}
