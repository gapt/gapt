package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.gaptic.tactics.AnalyticInductionTactic._
import at.logic.gapt.proofs.{ Ant, Sequent }

object prop_47 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/isaplanner/prop_47.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val mirror_definition = List(
    "mi1" -> hof"mirror(Leaf) = Leaf",
    "mi2" -> hof"∀l ∀y ∀r mirror(Node(l, y, r)) = Node(mirror(r), y, mirror(l))" )

  val max_definition = List(
    "ma1" -> hof"∀y max2(Z, y) = y",
    "ma2" -> hof"∀z max2(S(z), Z) = S(z)",
    "ma3" -> hof"∀z ∀x2 max2(S(z), S(x2)) = S(max2(z, x2))" )

  val max_comm_goal = hof"!x !y max2(x,y) = max2(y,x)"
  val max_comm = max_definition ++: Sequent() :+ "goal" -> max_comm_goal
  val max_comm_proof = Lemma( max_comm ) {
    analyticInduction withAxioms sequentialAxioms.forAllVariables.forLabel( "goal" )
  }

  val proof = Lemma( sequent ) {
    cut( "max_comm", max_comm_goal ); insert( max_comm_proof )
    allR; analyticInduction
  }

}
