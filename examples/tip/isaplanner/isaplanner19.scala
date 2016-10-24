package at.logic.gapt.examples.tip.isaplanner

import better.files._
import at.logic.gapt.expr._
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Context.{ InductiveType, Sort }
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.proofs.gaptic._

/* This is not a s.i.p. because of the nested induction. */
object isaplanner19 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( file"examples/tip/isaplanner/prop_19.smt2" )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val proof = Lemma( sequent ) {
    allR
    induction( hov"n:Nat" )
    // base case
    allR
    allL( "h8", le"xs:list" )
    eql( "h8_0", "goal" ).fromLeftToRight
    induction( hov"xs:list" )
    allL( "h3", le"Z:Nat" )
    eql( "h6", "goal" ).fromLeftToRight
    eql( "h3_0", "goal" ).fromLeftToRight
    refl

    allL( "h7", le"x:sk", le"xs_0:list" )
    allL( "h4", le"len(xs_0:list):Nat" )
    eql( "h7_0", "goal" )
    eql( "h4_0", "goal" ).fromLeftToRight
    refl

    // inductive case
    allR
    induction( hov"xs:list" )
    allL( "h9", le"n_0:Nat" )
    allL( "h3", le"S(n_0:Nat):Nat" )
    eql( "h9_0", "goal" ).fromLeftToRight
    eql( "h6", "goal" ).fromLeftToRight
    eql( "h3_0", "goal" ).fromLeftToRight
    refl
    allL( "h10", le"n_0:Nat", le"x:sk", le"xs_0:list" )
    allL( "h7", le"x:sk", le"xs_0:list" )
    allL( "h5", le"len(xs_0:list):Nat", le"n_0:Nat" )
    allL( "IHn_0", le"xs_0:list" )
    eql( "h10_0", "goal" )
    eql( "h7_0", "goal" )
    eql( "h5_0", "goal" )
    axiomLog
  }
}
