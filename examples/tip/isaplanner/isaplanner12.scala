package at.logic.gapt.examples.tip.isaplanner

import better.files._
import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Context.{ InductiveType, Sort }
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.proofs.gaptic._

object isaplanner12 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/isaplanner/prop_12.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val proof = Lemma( sequent ) {
    allR
    allR
    induction( hov"n:Nat" )
    // Base case
    allR
    allL( "h5", le"map2(f,xs:list):list" )
    allL( "h5", le"xs:list" )
    eql( "h5_0", "goal" ).fromLeftToRight
    eql( "h5_1", "goal" ).fromLeftToRight
    refl
    // Step case
    allR
    induction( hov"xs:list" )
    /// Base case
    rewrite.many ltr "h3"
    rewrite.many ltr "h6"
    rewrite.many ltr "h3"
    refl
    /// Step case
    rewrite.many ltr "h4"
    rewrite.many ltr "h7"
    chain( "IHn_0" )
  }
}
