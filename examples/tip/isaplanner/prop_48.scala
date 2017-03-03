package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.gaptic.tactics.AnalyticInductionTactic._
import at.logic.gapt.proofs.{ Ant, Sequent }

object prop_48 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/isaplanner/prop_48.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val dca_goal = hof"!xs (xs = nil ∨ ?x ?xss xs = cons(x, xss))"
  val dca = Sequent() :+ ( "goal" -> dca_goal )
  val dca_proof = Lemma( dca ) {
    allR; analyticInduction withAxioms standardAxioms.forVariables( hov"xs:list" ).forLabel( "goal" )
  }

  val manualProof = Lemma( ( "dca" -> hof"!xs (xs = nil ∨ ?x ?xss xs = cons(x, xss))" ) +: sequent ) {
    allR; induction( hov"xs:list" )
    //- IB
    impR; negL; axiomLog
    //- IC
    impR; negL;
    allL( "dca", hov"xs_0:list" )
    orL
    //- IC - 1
    eql( "dca_0", "goal_1" ).fromLeftToRight
    rewrite.many ltr "h9" in "goal_1"
    rewrite.many ltr "h6" in "goal_1"
    rewrite.many ltr "h11" in "goal_1"; refl
    //- IC - 2
    exL; exL
    rewrite.many ltr "dca_0" in "goal_1"
    rewrite.many ltr "h10" in "goal_1"
    rewrite.many ltr "h7" in "goal_1"
    rewrite.many ltr "h12" in "goal_1"; escargot
  }
}
