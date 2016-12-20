package at.logic.gapt.examples.tip.isaplanner

import better.files._
import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Context.{ InductiveType, Sort }
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.proofs.gaptic._

object isaplanner36 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/isaplanner/prop_36.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val proof = Lemma( sequent ) {
    allR
    induction( hov"xs:list" )
    // base case
    allL( "h2", le"lam" )
    axiomLog
    // inductive case
    allL( "h6", le"x:sk" )
    allL( "h4", le"lam", le"x:sk", le"xs_0:list" )
    andL
    impL( "h6_0_1" )
    forget( "goal" )
    prop // invoking axiomTop instead of prop throws an exception.
    impL( "h4_0" )
    axiomLog
    eql( "h4_0", "goal" )
    eql( "IHxs_0", "goal" ).fromLeftToRight
    refl
  }
}
