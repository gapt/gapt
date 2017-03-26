package at.logic.gapt.examples.tip.prod

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.provers.viper.aip.AnalyticInductionProver

object prop_28 extends TacticsProof {

  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/prod/prop_28.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val lemma = (
    ( "" -> hof"∀y append(nil2, y) = y" ) +:
    ( "" -> hof"∀z ∀xs ∀y append(cons2(z, xs), y) = cons2(z, append(xs, y))" ) +:
    Sequent() :+ ( "" -> hof"!xs append(xs,nil2) = xs" )
  )

  val lemma_proof = AnalyticInductionProver.singleInduction( lemma, hov"xs:list2" )

  val lemma_22 = (
    ( "" -> hof"∀y append(nil2, y) = y" ) +:
    ( "" -> hof"∀z ∀xs ∀y append(cons2(z, xs), y) = cons2(z, append(xs, y))" ) +:
    Sequent() :+ ( "" -> hof"!xs !ys !zs append(xs, append(ys, zs)) = append(append(xs,ys),zs)" )
  )

  val lemma_22_proof = AnalyticInductionProver.singleInduction( lemma_22, hov"xs:list2" )

  val cong_2 = (
    ( "" -> hof"!xs !ys !zs append(xs, append(ys, zs)) = append(append(xs,ys),zs)" ) +:
    ( "" -> hof"revflat(nil) = nil2" ) +:
    ( "" -> hof"∀xs ∀xss revflat(cons(xs, xss)) = append(revflat(xss), rev(xs))" ) +:
    ( "" -> hof"∀y qrevflat(nil, y) = y" ) +:
    ( "" -> hof"∀xs ∀xss ∀y qrevflat(cons(xs, xss), y) = qrevflat(xss, append(rev(xs), y))" ) +:
    ( "" -> hof"∀y append(nil2, y) = y" ) +:
    ( "" -> hof"∀z ∀xs ∀y append(cons2(z, xs), y) = cons2(z, append(xs, y))" ) +:
    Sequent() :+ ( "" -> hof"!xs !ys append(revflat(xs),ys) = qrevflat(xs, ys)" )
  )

  val cong_2_proof = AnalyticInductionProver.singleInduction( cong_2, hov"xs:list" )

  val proof = Lemma( sequent ) {
    cut( "lemma", hof"!xs append(xs,nil2) = xs" )
    insert( lemma_proof )
    cut( "lemma_22", hof"!xs !ys !zs append(xs, append(ys, zs)) = append(append(xs,ys),zs)" )
    insert( lemma_22_proof )
    cut( "cong_2", hof"!xs !ys append(revflat(xs),ys) = qrevflat(xs, ys)" )
    insert( cong_2_proof )
    allR; induction( hov"x:list" ); decompose.onAllSubGoals; repeat( escargot )
  }
}
