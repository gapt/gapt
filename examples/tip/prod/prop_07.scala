package at.logic.gapt.examples.tip.prod

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.provers.viper.aip.AnalyticInductionProver

object prop_07 extends TacticsProof {

  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/prod/prop_07.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val lem_1 = (
    ( "ap1" -> hof"∀y plus(Z, y) = y" ) +:
    ( "ap2" -> hof"∀z ∀y plus(S(z), y) = S(plus(z, y))" ) +:
    Sequent() :+ ( "lem_1" -> hof"∀x ∀y plus(x,S(y)) = S(plus(x,y))" ) )

  val lem_1_proof = AnalyticInductionProver.singleInduction( lem_1, hov"x:Nat" )

  val cut_lem = ( "lem_1" -> hof"∀x ∀y plus(x,S(y)) = S(plus(x,y))" ) +: sequent

  val cut_lem_proof = AnalyticInductionProver.singleInduction( cut_lem, hov"x:list" )

  val proof = Lemma( sequent ) {
    cut( "lem_1", hof"∀x ∀y plus(x,S(y)) = S(plus(x,y))" )
    insert( lem_1_proof )
    insert( cut_lem_proof )
  }
}
