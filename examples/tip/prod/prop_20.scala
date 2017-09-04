package at.logic.gapt.examples.tip.prod

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.provers.viper.aip.AnalyticInductionProver

object prop_20 extends TacticsProof {

  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/prod/prop_20.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val lemma = (
    ( "" -> hof"length(nil) = Z" ) +:
    ( "" -> hof"∀y ∀xs length(cons(y, xs)) = S(length(xs))" ) +:
    ( "" -> hof"∀y append(nil, y) = y" ) +:
    ( "" -> hof"∀z ∀xs ∀y append(cons(z, xs), y) = cons(z, append(xs, y))" ) +:
    Sequent() :+ ( "lemma" -> hof"∀xs ∀ys ∀y length(append(xs, cons(y,ys))) = S(length(append(xs, ys)))" ) )

  val lemma_proof = AnalyticInductionProver.singleInduction( lemma, hov"xs:list" )

  val proof = Lemma( sequent ) {
    cut( "lemma", hof"∀xs ∀ys ∀y length(append(xs, cons(y,ys))) = S(length(append(xs, ys)))" )
    insert( lemma_proof )
    allR; induction( hov"x:list" ); decompose.onAllSubGoals; repeat( escargot )
  }
}
