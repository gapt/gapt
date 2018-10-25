package gapt.examples

import gapt.expr._
import gapt.proofs.Sequent
import gapt.proofs.context.update.Sort
import gapt.proofs.gaptic._

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
