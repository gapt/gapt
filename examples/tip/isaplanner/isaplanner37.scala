package at.logic.gapt.examples.tip.isaplanner

import better.files._
import at.logic.gapt.expr._
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Context.{ InductiveType, Sort }
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.proofs.gaptic._

object isaplanner37 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( file"examples/tip/isaplanner/prop_37.smt2" )
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
    allL( "h9", le"x:Nat" )
    allL( "h7", le"x:Nat" )
    eql( "h9_0", "goal" ).fromLeftToRight
    axiomLog
    // inductive case
    decompose
    allL( "h10", le"x:Nat", le"x_0:Nat", le"xs_0:list" )
    impL
    negR
    allL( "h11", le"x:Nat", le"x_0:Nat", le"xs_0:list" )
    impL
    axiomLog
    eql( "h11_0", "goal" )
    axiomLog
    allL( "h8", le"x:Nat", le"x_0:Nat", le"delete(x:Nat,xs_0:list)" )
    andL
    impL( "h8_0_0" )
    eql( "h10_0", "goal" )
    axiomLog
    orL
    allL( "h11", le"x:Nat", le"x_0:Nat", le"xs_0:list" )
    impL( "h11_0" )
    axiomLog
    eql( "h11_0", "goal" )
    axiomLog
    axiomLog
  }
}
