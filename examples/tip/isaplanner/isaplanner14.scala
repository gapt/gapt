package at.logic.gapt.examples.tip.isaplanner

import better.files._
import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Context.{ InductiveType, Sort }
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.proofs.gaptic._

object isaplanner14 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/isaplanner/prop_14.smt2", getClass ) )
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
    allR
    allL( "h2", le"p:fun1" )
    allL( "h5", le"ys:list" )
    allL( "h5", le"filter(p:fun1, ys:list):list" )
    eql( "h2_0", "goal" ).fromLeftToRight
    eql( "h5_0", "goal" ).fromLeftToRight
    eql( "h5_1", "goal" ).fromLeftToRight
    refl
    // inductive case
    allR
    allL( "h6", le"x:sk", le"xs_0:list", le"ys:list" )
    eql( "h6_0", "goal" )
    allL( "h3", le"p:fun1", le"x:sk", le"append(xs_0:list, ys:list):list" )
    allL( "h4", le"p:fun1", le"x:sk", le"append(xs_0:list, ys:list):list" )
    impL( "h3_0" )
    negR
    impL( "h4_0" )
    axiomLog

    eql( "h4_0", "goal" )
    allL( "IHxs_0", le"ys:list" )
    eql( "IHxs_0_0", "goal" )
    allL( "h4", le"p:fun1", le"x:sk", le"xs_0:list" )
    impL( "h4_1" )
    axiomLog

    eql( "h4_1", "goal" )
    allL( "h6", le"x:sk",
      le"filter(p:fun1, xs_0:list):list",
      le"filter(p:fun1, ys:list):list" )
    eql( "h6_1", "goal" ).fromLeftToRight
    refl

    allL( "h3", le"p:fun1", le"x:sk", le"xs_0:list" )
    impL( "h3_1" )
    negR
    impL( "h4_0" )
    axiomLog

    allL( "h4", le"p:fun1", le"x:sk", le"xs_0:list" )
    impL( "h4_1" )
    axiomLog

    eql( "h4_1", "goal" )
    eql( "h4_0", "goal" )
    allL( "h6", le"x:sk",
      le"filter(p:fun1, xs_0:list):list",
      le"filter(p:fun1, ys:list):list" )
    eql( "h6_1", "goal" )
    allL( "IHxs_0", le"ys:list" )
    eql( "IHxs_0_0", "goal" ).fromLeftToRight
    refl

    eql( "h3_1", "goal" )
    eql( "h3_0", "goal" )
    allL( "IHxs_0", le"ys:list" )
    eql( "IHxs_0_0", "goal" ).fromLeftToRight
    refl
  }
}
