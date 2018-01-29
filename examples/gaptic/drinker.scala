package at.logic.gapt.examples

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.Sort
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._

object drinker extends TacticsProof {
  ctx += Sort( "i" )
  ctx += hoc"P: i>o"

  val drinker = Lemma( Sequent() :+ ( "D" -> hof"?x (P x -> !y P y)" ) ) {
    exR( fov"c" ); decompose
    exR( fov"y" ); decompose
    trivial
  }

  val dualdrinker = Lemma( ( "D" -> hof"!x (P x & ?y -P y)" ) +: Sequent() ) {
    allL( fov"c" ); decompose
    allL( fov"y" ); decompose
    trivial
  }
}
