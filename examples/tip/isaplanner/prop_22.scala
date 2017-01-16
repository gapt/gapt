package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Ant
import at.logic.gapt.proofs.gaptic._

/* This proof is not a s.i.p. because of the nested
 * inductions.
 */
object prop_22 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/isaplanner/prop_22.smt2", getClass ) )
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
    allL( "h1", le"max2(b:Nat,c:Nat):Nat" )
    eql( "h1_0", "goal" ).fromLeftToRight
    eql( "h1_1", "goal" ).fromLeftToRight
    refl
    // inductive case
    allR
    allR
    induction( hov"b:Nat" )
    allL( "h2", le"a_0:Nat" )
    allL( "h1", le"c:Nat" )
    eql( "h2_0", "goal" ).fromLeftToRight
    eql( "h1_0", "goal" ).fromLeftToRight
    refl

    allL( "h3", le"a_0:Nat", le"b_0:Nat" )
    eql( "h3_0", "goal" )
    induction( hov"c:Nat" )
    allL( "h2", le"max2(a_0:Nat, b_0:Nat):Nat" )
    eql( "h2_0", "goal" ).fromLeftToRight
    allL( "h2", le"b_0:Nat" )
    eql( "h2_1", "goal" ).fromLeftToRight
    eql( "h3_0", "goal" ).fromLeftToRight
    refl

    allL( "h3", le"b_0:Nat", le"c_0:Nat" )
    allL( "h3", le"a_0:Nat", le"max2(b_0:Nat,c_0:Nat):Nat" )
    eql( "h3_1", "goal" )
    eql( "h3_2", "goal" )
    allL( "h3", le"max2(a_0:Nat,b_0:Nat):Nat", le"c_0:Nat" )
    eql( "h3_3", "goal" )
    allL( "IHa_0", le"b_0:Nat", le"c_0:Nat" )
    eql( "IHa_0_0", "goal" ).fromLeftToRight
    refl
  }
}
