package at.logic.gapt.examples.tip.isaplanner

import better.files._
import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Context.{ InductiveType, Sort }
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.proofs.gaptic._

/* This proof is not a s.i.p. because of the subinductions */
object isaplanner33 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/isaplanner/prop_33.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val proof = Lemma( sequent ) {
    allR
    induction( hov"a:Nat" )
    // base case
    allR
    andR
    impR
    allL( "h4", le"b:Nat" )
    axiomLog

    impR
    allL( "h1", le"b:Nat" )
    eql( "h1_0", "goal_1" ).fromLeftToRight
    axiomLog

    // inductive case
    allR
    andR
    induction( hov"b:Nat" )
    allL( "h2", le"a_0:Nat" )
    allL( "h8", le"a_0:Nat" )
    eql( "h2_0", "goal" ).fromLeftToRight
    impR
    negL
    axiomLog
    allL( "h3", le"a_0:Nat", le"b_0:Nat" )
    allL( "IHa_0", le"b_0:Nat" )
    allL( "h10", le"min2(a_0:Nat, b_0:Nat):Nat", le"a_0:Nat" )
    allL( "h6", le"a_0:Nat", le"b_0:Nat" )
    eql( "h3_0", "goal" )
    impR
    andL( "h10_0" )
    impL( "h10_0_0" )
    axiomLog
    andL( "IHa_0_0" )
    impL( "IHa_0_0_0" )
    axiomLog
    andL( "h6_0" )
    impL( "h6_0_1" )
    axiomLog
    axiomLog
    induction( hov"b:Nat" )
    impR
    allL( "h5", le"a_0:Nat" )
    negL
    axiomLog
    allL( "h6", le"a_0:Nat", le"b_0:Nat" )
    allL( "IHa_0", le"b_0:Nat" )
    allL( "h10", le"min2(a_0:Nat, b_0:Nat):Nat", le"a_0:Nat" )
    allL( "h3", le"a_0:Nat", le"b_0:Nat" )
    andL( "h6_0" )
    andL( "IHa_0_0" )
    andL( "h10_0" )
    impR
    impL( "h6_0_0" )
    axiomLog
    impL( "IHa_0_0_1" )
    axiomLog
    impL( "h10_0_1" )
    axiomLog
    eql( "h3_0", "goal_1" )
    axiomLog
  }
}
