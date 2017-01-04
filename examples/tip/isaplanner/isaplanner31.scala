package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Ant
import at.logic.gapt.proofs.gaptic._

object isaplanner31 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/benchmarks/isaplanner/prop_31.smt2", getClass ) )
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
    allR
    allL( "h1", le"b:Nat" )
    allL( "h1", le"min2(b:Nat,c:Nat):Nat" )
    allL( "h1", le"c:Nat" )
    eql( "h1_0", "goal" ).fromLeftToRight
    eql( "h1_1", "goal" ).fromLeftToRight
    eql( "h1_2", "goal" ).fromLeftToRight
    refl
    // inductive case
    allR
    induction( hov"b:Nat" )
    allR
    allL( "h2", le"a_0:Nat" )
    allL( "h1", le"c:Nat" )
    eql( "h1_0", "goal" ).fromLeftToRight
    eql( "h2_0", "goal" ).fromLeftToRight
    eql( "h1_0", "goal" ).fromLeftToRight
    refl
    allR
    allL( "h3", le"a_0:Nat", le"b_0:Nat" )
    eql( "h3_0", "goal" )
    induction( hov"c:Nat" )
    allL( "h2", le"b_0:Nat" )
    allL( "h2", le"a_0:Nat" )
    allL( "h2", le"min2(a_0, b_0)" )
    eql( "h2_0", "goal" ).fromLeftToRight
    eql( "h2_1", "goal" ).fromLeftToRight
    eql( "h2_2", "goal" ).fromLeftToRight
    refl
    allL( "h3", le"min2(a_0:Nat, b_0:Nat):Nat", le"c_0:Nat" )
    allL( "h3", le"b_0:Nat", le"c_0:Nat" )
    allL( "h3", le"a_0:Nat", le"min2(b_0:Nat, c_0:Nat):Nat" )
    allL( "IHa_0", le"b_0:Nat", le"c_0:Nat" )
    eql( "h3_1", "goal" )
    eql( "h3_2", "goal" )
    eql( "h3_3", "goal" )
    eql( "IHa_0_0", "goal" ).fromLeftToRight
    refl
  }
}
