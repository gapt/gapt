package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Ant
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.provers.viper.{ AnalyticInductionProver, ProverOptions, escargot, independentInductionAxioms, sequentialInductionAxioms }

object prop_10 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/isaplanner/prop_10.smt2", getClass ) )
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

  val aipOptions1 = new ProverOptions( escargot, independentInductionAxioms )
  val proof2 = new AnalyticInductionProver( aipOptions1 ) lkProof ( sequent, "goal", List( hov"m:Nat" ) )

  val aipOptions2 = new ProverOptions( escargot, sequentialInductionAxioms )
  val proof3 = new AnalyticInductionProver( aipOptions2 ) lkProof ( sequent, "goal", List( hov"m:Nat" ) )

  val proof4 = Lemma( sequent ) { viper }
}
