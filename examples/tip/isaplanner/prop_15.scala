package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Ant
import at.logic.gapt.proofs.gaptic._

object isaplanner15 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/isaplanner/prop_15.smt2", getClass ) )
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
    allL( "h8", le"x:Nat" )
    allL( "h7", le"x:Nat", le"nil:list" )
    eql( "h8_0", "goal" )
    eql( "h7_0", "goal" ).fromLeftToRight
    refl
    // inductive case
    allL( "h7", le"x_0:Nat", le"xs_0:list" )
    allL( "h9", le"x:Nat", le"x_0:Nat", le"xs_0:list" )
    allL( "h10", le"x:Nat", le"x_0:Nat", le"xs_0:list" )
    eql( "h7_0", "goal" )
    impL( "h9_0" )
    negR
    impL( "h10_0" )
    axiomLog

    eql( "h10_0", "goal" )
    allL( "h7", le"x:Nat", le"cons(x_0:Nat,xs_0:list)" )
    eql( "h7_1", "goal" )
    eql( "h7_0", "goal" ).fromLeftToRight
    refl

    eql( "h9_0", "goal" )
    allL( "h7", le"x_0:Nat", le"ins(x:Nat, xs_0:list):list" )
    eql( "h7_1", "goal" )
    eql( "IHxs_0", "goal" ).fromLeftToRight
    refl
  }
}
