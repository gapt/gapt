package at.logic.gapt.examples.tip.prod

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.provers.viper.AnalyticInductionProver

object prop_30 extends TacticsProof {

  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/prod/prop_30.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val dca_goal = hof"!xs (xs = nil ∨ xs = cons(head(xs), tail(xs)))"

  val dca = (
    ( "" -> hof"∀x0 ∀x1 head(cons(x0, x1)) = x0" ) +:
    ( "" -> hof"∀x0 ∀x1 tail(cons(x0, x1)) = x1" ) +:
    Sequent() :+ ( "" -> dca_goal )
  )

  val dca_proof = AnalyticInductionProver.singleInduction( dca, hov"xs:list" )

  val lemma_11_goal = hof"!xs !y !zs append(append(xs, cons(y,nil)), zs) = append(xs, cons(y,zs))"

  val lemma_11 = (
    ( "" -> hof"∀y append(nil, y) = y" ) +:
    ( "" -> hof"∀z ∀xs ∀y append(cons(z, xs), y) = cons(z, append(xs, y))" ) +:
    ( "" -> hof"rev(nil) = nil" ) +:
    ( "" -> hof"∀y ∀xs rev(cons(y, xs)) = append(rev(xs), cons(y, nil))" ) +:
    Sequent() :+ ( "" -> lemma_11_goal )
  )

  val lemma_11_proof = AnalyticInductionProver.singleInduction( lemma_11, hov"xs:list" )

  val cong_5_goal = hof"!xs !ys rev(append(rev(xs),ys)) = append(rev(ys),xs)"

  val cong_5 = (
    ( "" -> hof"∀y append(nil, y) = y" ) +:
    ( "" -> hof"∀z ∀xs ∀y append(cons(z, xs), y) = cons(z, append(xs, y))" ) +:
    ( "" -> hof"rev(nil) = nil" ) +:
    ( "" -> hof"∀y ∀xs rev(cons(y, xs)) = append(rev(xs), cons(y, nil))" ) +:
    ( "" -> dca_goal ) +:
    ( "" -> lemma_11_goal ) +:
    Sequent() :+ ( "" -> cong_5_goal )
  )

  val cong_5_proof = AnalyticInductionProver.singleInduction( cong_5, hov"xs:list" )

  val proof = Lemma( sequent ) {
    cut( "dca", dca_goal ); insert( dca_proof )
    cut( "lemma_11", lemma_11_goal ); insert( lemma_11_proof )
    cut( "cong_5", cong_5_goal ); insert( cong_5_proof )
    escargot
  }

}
