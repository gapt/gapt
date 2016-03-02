package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._

object fol1 {
  val p = Lemma( Sequent(
    Seq( "L" -> fof"(all x all y (P(x,y) -> Q(x,y)))" ),
    Seq( "R" -> fof"(exists x exists y (-Q(x,y) -> -P(x,y)))" )
  ) ) {

    cut( fof"(all x exists y (-P(x,y) | Q(x,y)))", "C" )

    // left subproof
    allR( "C" )
    exR( "C", fot"a" )
    allL( "L", fot"x", fot"a" )
    decompose
    destruct( "L_0" )
    repeat( axiomLog )

    // right subproof
    allL( "C", fot"b" )
    exL( "C_0" )
    exR( "R", fot"b", fot"y" )
    destruct( "C_0" )
    repeat( decompose andThen axiomLog )
  }
}
