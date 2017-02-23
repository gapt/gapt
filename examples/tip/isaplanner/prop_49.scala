package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Ant
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.gaptic.tactics.AnalyticInductionTactic._

object prop_49 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/isaplanner/prop_49.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val listType = bench.datatypes( 1 )

  val proof = Lemma( sequent ) {
    cut( "cf", hof"∀ys ∀xs butlast(append(xs, ys)) = butlastConcat(xs, ys)" ); forget( "goal" )
    //- cut
    allR
    induction( hov"ys:list" )
    //- cut - IB
    allR
    rewrite ltr "h7" in "cf"
    analyticInduction withAxioms sequentialAxioms.forVariables( hov"xs:list" ).forFormula( hof"!xs append(xs,nil) = xs" )
    //- cut - IC
    allR; induction( hov"xs:list" )
    //- cut - IC - IB
    escargot
    //- cut - IC - IC
    analyticInduction withAxioms tipDomainClosure.forTypes( listType )
    //-
    escargot
  }
}
