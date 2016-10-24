package at.logic.gapt.examples.tip.isaplanner

import better.files._
import at.logic.gapt.expr._
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Context.{ InductiveType, Sort }
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.proofs.gaptic._

object isaplanner21 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( file"examples/tip/isaplanner/prop_21.smt2" )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val proof = Lemma( sequent ) {
    allR
    induction( hov"n:Nat" )
    // base case
    allR
    allL( "h3", le"plus(Z:Nat, m:Nat):Nat" )
    axiomLog
    // inductive case
    allR
    allL( "h2", le"n_0:Nat", le"m:Nat" )
    eql( "h2_0", "goal" )
    allL( "h5", le"n_0:Nat", le"plus(n_0:Nat,m:Nat):Nat" )
    andL
    impL( "h5_0_1" )
    allL( "IHn_0", le"m:Nat" )
    axiomLog

    axiomLog
  }
}
