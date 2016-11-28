package at.logic.gapt.examples.tip.isaplanner

import better.files._
import at.logic.gapt.expr._
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Context.{ InductiveType, Sort }
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.provers.viper.{ AnalyticInductionProver, independentInductionAxioms, sequentialInductionAxioms }

object isaplanner10 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( file"examples/tip/isaplanner/prop_10.smt2" )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val proof = Lemma( sequent ) {
    allR
    induction( hov"m:Nat" )
    // base case
    allL( "h1", le"Z:Nat" )
    forget( "h0", "h1", "h2", "h3", "h4" )
    axiomLog

    // Inductive case
    allL( "h3", le"m_0:Nat", le"m_0:Nat" )
    forget( "h0", "h1", "h2", "h3", "h4" )
    eql( "h3_0", "goal" )
    axiomLog
  }

  val proof2 = AnalyticInductionProver( sequent, "goal", List( hov"m:Nat" ), independentInductionAxioms ) get

  val proof3 = AnalyticInductionProver( sequent, "goal", List( hov"m:Nat" ), sequentialInductionAxioms ) get
}
