package at.logic.gapt.examples.tip.prod

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.provers.viper.AnalyticInductionProver

object prop_27 extends TacticsProof {

  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/prod/prop_27.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val lemma_22 = (
    ( "" -> hof"∀y append(nil, y) = y" ) +:
    ( "" -> hof"∀z ∀xs ∀y append(cons(z, xs), y) = cons(z, append(xs, y))" ) +:
    Sequent() :+ ( "" -> hof"!xs !ys !zs append(xs, append(ys, zs)) = append(append(xs,ys),zs)" )
  )

  val lemma_22_proof = AnalyticInductionProver.singleInduction( lemma_22, hov"xs:list" )

  val cong_1 = (
    ( "" -> hof"∀y qrev(nil, y) = y" ) +:
    ( "" -> hof"∀z ∀xs ∀y qrev(cons(z, xs), y) = qrev(xs, cons(z, y))" ) +:
    ( "" -> hof"rev(nil) = nil" ) +:
    ( "" -> hof"∀y ∀xs rev(cons(y, xs)) = append(rev(xs), cons(y, nil))" ) +:
    ( "" -> hof"∀y append(nil, y) = y" ) +:
    ( "" -> hof"∀z ∀xs ∀y append(cons(z, xs), y) = cons(z, append(xs, y))" ) +:
    ( "" -> hof"!xs !ys !zs append(xs, append(ys, zs)) = append(append(xs,ys),zs)" ) +:
    Sequent() :+ ( "" -> hof"!xs !ys append(rev(xs),ys) = qrev(xs, ys)" )
  )

  val cong_1_proof = AnalyticInductionProver.singleInduction( cong_1, hov"xs:list" )

  val proof = Lemma( sequent ) {
    cut( "lemma_22", hof"!xs !ys !zs append(xs, append(ys, zs)) = append(append(xs,ys),zs)" )
    insert( lemma_22_proof )
    cut( "cong_1", hof"!xs !ys append(rev(xs),ys) = qrev(xs, ys)" )
    insert( cong_1_proof )
    allR; induction( hov"x:list" ); decompose.onAllSubGoals; repeat( escargot )
  }
}
