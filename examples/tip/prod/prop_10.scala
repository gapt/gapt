package at.logic.gapt.examples.tip.prod

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.provers.viper.aip.AnalyticInductionProver

object prop_10 extends TacticsProof {

  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/prod/prop_10.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val lemma_8 = (
    ( "aa1" -> hof"∀y append(nil, y) = y" ) +:
    ( "aa2" -> hof"∀z ∀xs ∀y append(cons(z, xs), y) = cons(z, append(xs, y))" ) +:
    ( "ar1" -> hof"rev(nil) = nil" ) +:
    ( "ar2" -> hof"∀y ∀xs rev(cons(y, xs)) = append(rev(xs), cons(y, nil))" ) +:
    Sequent() :+ ( "lemma_8" -> hof"∀xs ∀x rev(append(xs, cons(x,nil))) = append(cons(x,nil), rev(xs))" )
  )

  val lemma_8_proof = AnalyticInductionProver.singleInduction( lemma_8, hov"xs:list" )

  val proof = Lemma( sequent ) {
    cut( "lemma_8", hof"∀xs ∀x rev(append(xs, cons(x,nil))) = append(cons(x,nil), rev(xs))" )
    insert( lemma_8_proof )
    allR; induction( hov"x:list" ); decompose.onAllSubGoals; repeat( escargot )
  }
}
