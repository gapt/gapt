package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Ant
import at.logic.gapt.proofs.gaptic._

object isaplanner30 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/benchmarks/isaplanner/prop_30.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val proof = Lemma( sequent ) {
    allR
    allR
    induction( hov"xs:list" )
    // base case
    allL( "h6", le"x:Nat" )
    eql( "h6_0", "goal" )
    allL( "h14", le"x:Nat", le"x:Nat", le"nil:list" )
    andL
    impL( "h14_0_1" )
    orR
    induction( hov"x:Nat", "h14_0_1_0" )
    axiomLog
    allL( "h12", le"x_0:Nat", le"x_0:Nat" )
    andL
    impL( "h12_0_1" )
    axiomLog
    axiomLog
    axiomLog
    // inductive case
    allL( "h7", le"x:Nat", le"x_0:Nat", le"xs_0:list" )
    allL( "h8", le"x:Nat", le"x_0:Nat", le"xs_0:list" )
    impL( "h7_0" )
    negR
    impL( "h8_0" )
    axiomLog
    eql( "h8_0", "goal" )
    allL( "h14", le"x:Nat", le"x:Nat", le"cons(x_0:Nat, xs_0:list):list" )
    andL
    impL( "h14_0_1" )
    orR
    // proof of equal(x,x)
    induction( hov"x:Nat", "h14_0_1_0" )
    axiomLog
    allL( "h12", le"x_1:Nat", le"x_1:Nat" )
    andL
    impL( "h12_0_1" )
    axiomLog
    axiomLog

    axiomLog
    eql( "h7_0", "goal" )
    allL( "h14", le"x:Nat", le"x_0:Nat", le"ins(x:Nat, xs_0:list):list" )
    andL
    impL( "h14_0_1" )
    orR
    axiomLog
    axiomLog
  }
}
