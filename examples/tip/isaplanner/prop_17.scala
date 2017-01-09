package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Ant
import at.logic.gapt.proofs.gaptic._

object isaplanner17 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/isaplanner/prop_17.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val proof = Lemma( sequent ) {
    allR
    induction( hov"n:Nat" )
    // base case
    allL( "h1", le"Z:Nat" )
    forget( "h0", "h1", "h2", "h3", "h5", "h6", "h7", "h8" )
    andR
    impR
    axiomLog

    impR
    axiomLog
    // inductive case
    allL( "h2", le"n_0:Nat" )
    allL( "h6", le"n_0:Nat" )
    forget( "h0", "h1", "h2", "h3", "h5", "h6", "h7", "h8" )
    andR
    impR
    negL( "h2_0" )
    axiomLog

    impR
    negL( "h6_0" )
    axiomLog
  }
}
