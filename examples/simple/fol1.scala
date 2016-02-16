package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._

object fol1 {
  val p = Lemma( Sequent(
    Seq( "L" -> p9f"(all x all y (P(x,y) -> Q(x,y)))" ),
    Seq( "R" -> p9f"(exists x exists y (-Q(x,y) -> -P(x,y)))" )
  ) ) {

    cut( p9f"(all x exists y (-P(x,y) | Q(x,y)))", "C" )

    // left subproof
    allR( "C" )
    exR( "C", p9t"a" )
    allL( "L", p9t"x", p9t"a" )
    decompose
    destruct( "L_0" )
    repeat( axiomLog )

    // right subproof
    allL( "C", p9t"b" )
    exL( "C_0" )
    exR( "R", p9t"b", p9t"y" )
    destruct( "C_0" )
    repeat( decompose andThen axiomLog )
  }
}
