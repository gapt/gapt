package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.{ Ant, Sequent }

object isaplanner35 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/benchmarks/isaplanner/prop_35.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val domainClosureAxiom = hof"xs = nil ∨ xs = cons(head(xs),tail(xs))"

  val proofDca = Lemma(
    sequent.antecedent ++: Sequent() :+ ( "dca" -> domainClosureAxiom )
  ) {
      induction( hov"xs:list" )
      orR
      refl
      orR
      forget( "dca_0" )
      allL( "h0", le"x:sk", le"xs_0:list" )
      allL( "h1", le"x:sk", le"xs_0:list" )
      eql( "h0_0", "dca_1" ).fromLeftToRight
      eql( "h1_0", "dca_1" ).fromLeftToRight
      refl

    }

  val proof = Lemma( sequent ) {
    allR
    cut( "dca", domainClosureAxiom )
    forget( "goal" )
    insert( proofDca )
    orL
    eql( "dca", "goal" )
    allL( "h2", le"lam" )
    axiomLog
    eql( "dca", "goal" )
    allL( "h6", le"head(xs:list):sk" )
    allL( "h3", le"lam", le"head(xs:list):sk", le"tail(xs:list):list" )
    andL( "h6_0" )
    impL( "h3_0" )
    negR
    impL( "h6_0_0" )
    axiomLog
    axiomBot
    axiomLog
  }
}
