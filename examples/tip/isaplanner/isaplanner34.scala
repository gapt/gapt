package at.logic.gapt.examples.tip.isaplanner

import better.files._
import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Context.{ InductiveType, Sort }
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.proofs.gaptic._

/* This proof is not a s.i.p. because of the subinductions. */
object isaplanner34 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/isaplanner/prop_34.smt2", getClass ) )
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
    allL( "h4", le"Z:Nat" )
    andR
    induction( hov"b:Nat" )
    impR
    axiomLog
    impR
    allL( "h1", le"S(b_0:Nat):Nat" )
    allL( "h8", le"b_0:Nat" )
    negL
    eql( "h1_0", "goal_0" ).fromLeftToRight
    axiomLog
    induction( hov"b:Nat" )
    impR
    allL( "h1", le"Z:Nat" )
    eql( "h1_0", "goal_1" ).fromLeftToRight
    axiomLog
    allL( "h5", le"b_0:Nat" )
    impR
    negL
    axiomLog
    // inductive case
    allR
    induction( hov"b:Nat" )
    andR
    allL( "h4", le"S(a_0:Nat):Nat" )
    impR
    axiomLog
    allL( "h2", le"a_0:Nat" )
    impR
    eql( "h2_0", "goal_1" ).fromLeftToRight
    axiomLog
    andR
    allL( "h3", le"a_0:Nat", le"b_0:Nat" )
    allL( "h10", le"min2(a_0:Nat,b_0:Nat):Nat", le"b_0:Nat" )
    allL( "h6", le"b_0:Nat", le"a_0:Nat" )
    allL( "IHa_0", le"b_0:Nat" )
    eql( "h3_0", "goal" )
    impR
    andL( "h10_0" )
    andL( "h6_0" )
    andL( "IHa_0_0" )
    forget( "IHa_0_0_1", "h10_0_1", "h6_0_0" )
    impL( "h10_0_0" )
    axiomLog
    impL( "IHa_0_0_0" )
    axiomLog
    impL( "h6_0_1" )
    axiomLog
    axiomLog
    allL( "h6", le"b_0:Nat", le"a_0:Nat" )
    allL( "h10", le"min2(a_0:Nat, b_0:Nat):Nat", le"b_0:Nat" )
    allL( "IHa_0", le"b_0:Nat" )
    allL( "h3", le"a_0:Nat", le"b_0:Nat" )
    andL( "h6_0" )
    andL( "h10_0" )
    andL( "IHa_0_0" )
    forget( "h6_0_1", "IHa_0_0_0", "h10_0_0" )
    eql( "h3_0", "goal" )
    impR
    impL( "h6_0_0" )
    axiomLog
    impL( "IHa_0_0_1" )
    axiomLog
    impL( "h10_0_1" )
    axiomLog
    axiomLog
  }
}
