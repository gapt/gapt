package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Ant
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.provers.viper.aip.axioms.{ IndependentInductionAxioms, SequentialInductionAxioms }
import at.logic.gapt.provers.viper.aip.provers.escargot
import at.logic.gapt.provers.viper.aip.{ AnalyticInductionProver, ProverOptions }

object prop_10 extends TacticsProof {

  val bench = def_prop_10.loadProblem
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

  val aipOptions1 = new ProverOptions( escargot, IndependentInductionAxioms().forVariables( List( hov"m:Nat" ) ).forLabel( "goal" ) )
  val proof2 = new AnalyticInductionProver( aipOptions1 ) lkProof ( sequent ) get

  val aipOptions2 = new ProverOptions( escargot, SequentialInductionAxioms().forVariables( List( hov"m:Nat" ) ).forLabel( "goal" ) )
  val proof3 = new AnalyticInductionProver( aipOptions2 ) lkProof ( sequent ) get

  val proof4 = Lemma( sequent ) { treeGrammarInduction }
}
