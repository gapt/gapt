package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Ant
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.provers.viper.{ AnalyticInductionProver, ProverOptions, escargot, independentInductionAxioms }

/* This proof is not a s.i.p because of the subinduction,
 * in the base case of the primary induction.
 */
object prop_07 extends TacticsProof {

  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/isaplanner/prop_07.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val proof = Lemma( sequent ) {
    allR
    induction( hov"n:Nat" )
    // Base case
    allR
    allL( "h1", le"m:Nat" )
    eql( "h1_0", "goal" ).fromLeftToRight
    allL( "h3", le"Z:Nat" )
    induction( hov"m:Nat" )
    //base case
    axiomLog
    //inductive case
    allL( "h4", le"m_0:Nat" )
    axiomLog

    // Inductive case
    allR
    forget( "h0", "h1", "h3", "h4", "h6" )
    allL( "IHn_0", le"m:Nat" )
    allL( "h2", le"n_0:Nat", le"m:Nat" )
    allL( "h5", le"plus(n_0:Nat, m:Nat):Nat", le"n_0:Nat" )
    forget( "h2", "h5" )
    eql( "h2_0", "goal" )
    eql( "h5_0", "goal" )
    axiomLog

  }

  val aipOptions = new ProverOptions( escargot, independentInductionAxioms )
  val proof2 = new AnalyticInductionProver( aipOptions ) lkProof ( sequent, "goal", List( hov"n:Nat", hov"m:Nat" ) )
}
