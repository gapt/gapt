package at.logic.gapt.examples.tip.isaplanner

import better.files._
import at.logic.gapt.expr._
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Context.{ InductiveType, Sort }
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.proofs.gaptic._

object isaplanner26 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( file"examples/tip/isaplanner/prop_26.smt2" )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val proof = Lemma( sequent ) {
    allR
    allR
    induction( hov"xs:list" )
    // base case
    allR
    impR
    allL( "h7", le"x:Nat" )
    negL( "h7_0" )
    axiomLog
    allR
    impR
    allL( "h8", le"x:Nat", le"x_0:Nat", le"xs_0:list" )
    andL( "h8_0" )
    impL( "h8_0_0" )
    axiomLog
    orL( "h8_0_0" )
    allL( "h10", le"x_0:Nat", le"xs_0:list", le"ys:list" )
    eql( "h10_0", "goal_1" ).fromLeftToRight

    allL( "h8", le"x:Nat", le"x_0:Nat", le"append(xs_0:list, ys:list):list" )
    andL( "h8_1" )
    impL( "h8_1_1" )
    orR( "h8_1_1" )
    axiomLog
    axiomLog

    allL( "h10", le"x_0:Nat", le"xs_0:list", le"ys:list" )
    eql( "h10_0", "goal_1" ).fromLeftToRight
    allL( "h8", le"x:Nat", le"x_0:Nat", le"append(xs_0:list, ys:list):list" )
    andL( "h8_1" )
    impL( "h8_1_1" )
    orR( "h8_1_1" )
    allL( "IHxs_0", le"ys:list" )
    impL( "IHxs_0_0" )
    axiomLog
    axiomLog
    axiomLog
  }
}
