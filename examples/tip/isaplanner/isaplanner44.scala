package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Ant
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.provers.viper.{ AnalyticInductionProver, ProverOptions, escargot, independentInductionAxioms }
import better.files._

object isaplanner44 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( file"examples/tip/isaplanner/prop_44.smt2" )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val aipOptions = new ProverOptions( escargot, independentInductionAxioms )
  val proof1 = new AnalyticInductionProver( aipOptions ) lkProof ( sequent, "goal", List( hov"ys:list2" ) )
}
