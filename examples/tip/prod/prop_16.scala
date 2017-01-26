package at.logic.gapt.examples.tip.prod

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.provers.viper.AnalyticInductionProver

object prop_16 extends TacticsProof {

  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/prod/prop_16.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val lemma_1 = (
    ( "ap1" -> hof"∀y plus(Z, y) = y" ) +:
    ( "ap2" -> hof"∀z ∀y plus(S(z), y) = S(plus(z, y))" ) +:
    Sequent() :+ ( "" -> hof"∀x ∀y plus(x, S(y)) = S(plus(x,y))" )
  )

  val lemma_1_proof = AnalyticInductionProver.singleInduction( lemma_1, hov"x:Nat" )

  val proof = Lemma( sequent ) {
    cut( "lemma_1", hof"∀x ∀y plus(x, S(y)) = S(plus(x,y))" )
    insert( lemma_1_proof )
    allR; induction( hov"x:Nat" ); decompose.onAllSubGoals; repeat( escargot )
  }
}
