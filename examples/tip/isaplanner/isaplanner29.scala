package at.logic.gapt.examples.tip.isaplanner

import better.files._
import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Context.{ InductiveType, Sort }
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.proofs.gaptic._

/* This is not a s.i.p because of the nested induction which is
 * required to prove equal(x,x).
 */
object isaplanner29 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/isaplanner/prop_29.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val proof = Lemma( sequent ) {
    allR
    allR
    induction( hov"xs:list" )
    allL( "h7", le"x:Nat" )
    eql( "h7_0", "goal" )
    allL( "h11", le"x:Nat", le"x:Nat", le"nil:list" )
    andL
    impL( "h11_0_1" )
    orR
    induction( hov"x:Nat", "h11_0_1_0" )
    axiomLog
    allL( "h6", le"x_0:Nat", le"x_0:Nat" )
    andL
    impL( "h6_0_1" )
    axiomLog
    axiomLog
    axiomLog
    allL( "h8", le"x:Nat", le"x_0:Nat", le"xs_0:list" )
    impL
    negR
    allL( "h9", le"x:Nat", le"x_0:Nat", le"xs_0:list" )
    impL
    axiomLog
    eql( "h9_0", "goal" ).fromLeftToRight
    allL( "h11", le"x:Nat", le"x_0:Nat", le"xs_0:list" )
    andL
    impL( "h11_0_1" )
    orR
    axiomLog
    axiomLog
    eql( "h8_0", "goal" )
    allL( "h11", le"x:Nat", le"x_0:Nat", le"ins1(x:Nat, xs_0:list):list" )
    andL
    impL( "h11_0_1" )
    orR
    axiomLog
    axiomLog
  }
}
