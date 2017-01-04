package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._

object drinker {
  val drinker = Lemma( Sequent() :+ ( "D" -> hof"?x (P x -> !y P y)" ) ) {
    exR( le"c" ); decompose
    exR( le"y" ); decompose
    trivial
  }

  val dualdrinker = Lemma( ( "D" -> hof"!x (P x & ?y -P y)" ) +: Sequent() ) {
    allL( le"c" ); decompose
    allL( le"y" ); decompose
    trivial
  }
}
