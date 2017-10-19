package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Ant
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.provers.viper.aip.axioms.IndependentInductionAxioms
import at.logic.gapt.provers.viper.aip.provers.escargot
import at.logic.gapt.provers.viper.aip.{ AnalyticInductionProver, ProverOptions }

object prop_44 extends TacticsProof {

  val bench = def_prop_44.loadProblem
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val aipOptions = new ProverOptions( escargot, IndependentInductionAxioms().forVariables( List( hov"ys:list2" ) ).forLabel( "goal" ) )
  val proof1 = new AnalyticInductionProver( aipOptions ) lkProof ( sequent ) get
}
