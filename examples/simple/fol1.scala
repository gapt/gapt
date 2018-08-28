package gapt.examples

import gapt.expr._
import gapt.proofs.Sequent
import gapt.proofs.context.Context
import gapt.proofs.gaptic._

object fol1 extends TacticsProof {
  ctx += Context.Sort( "i" )
  ctx += hoc"P: i>i>o"
  ctx += hoc"Q: i>i>o"
  ctx += hoc"a: i"
  ctx += hoc"b: i"

  val proof = Lemma( hols"L: !x!y (P x y -> Q x y) :- R: ?x?y (-Q x y -> - P x y)" ) {
    cut( "C", fof"!x?y (-P x y | Q x y)" )

    // left subproof
    allR( "C" )
    exR( "C", fot"a" )
    allL( "L", fov"x", fot"a" )
    decompose
    destruct( "L_0" )
    repeat( axiomLog )

    // right subproof
    allL( "C", fot"b" )
    exL( "C_0" )
    exR( "R", fot"b", fov"y" )
    destruct( "C_0" )
    repeat( decompose andThen axiomLog )
  }
}
