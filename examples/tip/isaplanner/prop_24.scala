package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Ant
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.provers.viper.aip.axioms.SequentialInductionAxioms
import at.logic.gapt.provers.viper.aip.provers.escargot
import at.logic.gapt.provers.viper.aip.{ AnalyticInductionProver, ProverOptions }

/* This proof is not a s.i.p. */
object prop_24 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/isaplanner/prop_24.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  /* This proof uses induction on the goal, and subinductions on some
   * subformulas of the goal. These subinductions do not use their induction
   * hypothesis and are therefore merely case distinctions.
   */
  val proof1 = Lemma( sequent ) {
    allR
    induction( hov"a:Nat" )
    allR
    andR
    allL( "h1", le"b:Nat" )
    eql( "h1_0", "goal" ).fromLeftToRight
    induction( hov"b:Nat" )
    impR
    allL( "h4", le"Z" )
    axiomLog
    impR
    allL( "h9", le"b_0:Nat" )
    negL
    axiomLog
    allL( "h1", le"b:Nat" )
    eql( "h1_0", "goal" ).fromLeftToRight
    induction( hov"b:Nat" )
    impR
    axiomLog
    impR
    allL( "h5", le"b_0:Nat" )
    negL
    axiomLog
    allR
    andR
    // In order to continue we need again to do a case distinction
    // on b. It seems preferable to apply induction before decomposing the formula.
    induction( hov"b:Nat" )
    allL( "h2", le"a_0:Nat" )
    eql( "h2_0", "goal" ).fromLeftToRight
    impR
    allL( "h4", le"S(a_0:Nat)" )
    axiomLog
    allL( "h3", le"a_0:Nat", le"b_0:Nat" )
    eql( "h3_0", "goal" ).fromLeftToRight
    impR
    allL( "h10", le"max2(a_0:Nat, b_0:Nat):Nat", le"a_0:Nat" )
    andL( "h10_0" )
    forget( "h10_0_1" )
    impL( "h10_0_0" )
    axiomLog
    allL( "h6", le"b_0:Nat", le"a_0:Nat" )
    andL( "h6_0" )
    forget( "h6_0_0" )
    impL( "h6_0_1" )
    allL( "IHa_0", le"b_0:Nat" )
    andL( "IHa_0_0" )
    forget( "IHa_0_0_1" )
    impL( "IHa_0_0_0" )
    axiomLog
    axiomLog
    axiomLog

    induction( hov"b:Nat" )
    impR
    allL( "h2", le"a_0:Nat" )
    eql( "h2_0", "goal_1" ).fromLeftToRight
    // Now we need to prove equal(S(a_0),S(a_0)). This reduces via the axioms
    // to equal(a_0, a_0). But proving this requires a separate induction and this
    // cannot be done with the analytical induction provided by the sequential
    // axioms.
    allL( "h10", le"a_0:Nat", le"a_0:Nat" )
    andL( "h10_0" )
    forget( "h10_0_0" )
    impL( "h10_0_1" )
    forget( "goal_1" )
    induction( hov"a_0:Nat" )
    axiomLog
    allL( "h10", le"a_1:Nat", le"a_1:Nat" )
    andL( "h10_1" )
    forget( "h10_1_0" )
    impL( "h10_1_1" )
    axiomLog
    axiomLog
    axiomLog
    impR
    allL( "h6", le"b_0:Nat", le"a_0:Nat" )
    andL( "h6_0" )
    forget( "h6_0_1" )
    impL( "h6_0_0" )
    axiomLog
    allL( "h3", le"a_0:Nat", le"b_0:Nat" )
    eql( "h3_0", "goal_1" ).fromLeftToRight
    allL( "h10", le"max2(a_0:Nat, b_0:Nat):Nat", le"a_0:Nat" )
    andL( "h10_0" )
    forget( "h10_0_0" )
    allL( "IHa_0", le"b_0:Nat" )
    andL( "IHa_0_0" )
    forget( "IHa_0_0_0" )
    impL( "IHa_0_0_1" )
    axiomLog
    impL( "h10_0_1" )
    axiomLog
    axiomLog
  }

  val options = new ProverOptions( escargot, SequentialInductionAxioms().forAllVariables.forLabel( "goal" ) )
  val proof2 = new AnalyticInductionProver( options ) lkProof ( ( "refl" -> hof"!x equal(x,x)" ) +: sequent ) get
}
