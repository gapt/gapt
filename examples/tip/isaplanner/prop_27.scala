package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Ant
import at.logic.gapt.proofs.gaptic._

object prop_27 extends TacticsProof {

  val bench = def_prop_27.loadProblem
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val proof = Lemma( sequent ) {
    allR
    allR
    induction( hov"xs:list" )
    allR
    allL( "h9", le"ys:list" )
    eql( "h9_0", "goal" ).fromLeftToRight
    impR
    axiomLog
    allR
    allL( "h10", le"x_0:Nat", le"xs_0:list", le"ys:list" )
    eql( "h10_0", "goal" )
    allL( "h8", le"x:Nat", le"x_0:Nat", le"append(xs_0:list, ys:list):list" )
    andL( "h8_0" )
    impR
    impL( "h8_0_1" )
    orR
    allL( "IHxs_0", le"ys:list" )
    impL( "IHxs_0_0" )
    axiomLog
    axiomLog
    axiomLog
  }
}
