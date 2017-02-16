package at.logic.gapt.examples.tip.prod

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.provers.viper.aip.AnalyticInductionProver

object prop_08 extends TacticsProof {

  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/prod/prop_08.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val lemma_ldca = (
    ( "h0" -> hof"∀x0 ∀x1 head(cons(x0, x1)) = x0" ) +:
    ( "h1" -> hof"∀x0 ∀x1 tail(cons(x0, x1)) = x1" ) +:
    Sequent() :+ ( "dca" -> hof"∀xs (xs = nil ∨ xs = cons(head(xs), tail(xs)))" )
  )

  val lemma_ldca_proof = AnalyticInductionProver.singleInduction( lemma_ldca, hov"xs:list" )

  val lemma_ndca = (
    ( "h2" -> hof"∀x0 p(S(x0)) = x0" ) +:
    Sequent() :+ ( "dca" -> hof"∀x (x = Z ∨ x = S(p(x)))" )
  )

  val lemma_ndca_proof = AnalyticInductionProver.singleInduction( lemma_ndca, hov"x:Nat" )

  val lemma_4 = (
    ( "ndca" -> hof"∀x (x = Z ∨ x = S(p(x)))" ) +:
    ( "ldca" -> hof"∀xs (xs = nil ∨ xs = cons(head(xs), tail(xs)))" ) +:
    ( "ad1" -> hof"∀y drop(Z, y) = y" ) +:
    ( "ad2" -> hof"∀z drop(S(z), nil) = nil" ) +:
    ( "ad3" -> hof"∀z ∀x2 ∀x3 drop(S(z), cons(x2, x3)) = drop(z, x3)" ) +:
    Sequent() :+ ( "lemma_4" -> hof"∀y ∀zs ∀x ∀z drop(S(x), drop(y,cons(z,zs))) = drop(x, drop(y,zs))" )
  )

  val lemma_4_proof = AnalyticInductionProver.singleInduction( lemma_4, hov"y:Nat" )

  val proof = Lemma( sequent ) {
    cut( "ndca", hof"∀x (x = Z ∨ x = S(p(x)))" )
    insert( lemma_ndca_proof )
    cut( "ldca", hof"∀xs (xs = nil ∨ xs = cons(head(xs), tail(xs)))" )
    insert( lemma_ldca_proof )
    cut( "lemma_4", hof"∀y ∀zs ∀x ∀z drop(S(x), drop(y,cons(z,zs))) = drop(x, drop(y,zs))" )
    insert( lemma_4_proof )
    allR; induction( hov"x:Nat" ); decompose.onAllSubGoals; repeat( escargot )
  }
}
