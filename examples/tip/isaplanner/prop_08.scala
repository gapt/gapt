package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.{ Ant, Sequent }
import at.logic.gapt.provers.viper.aip.axioms.{ IndependentInductionAxioms, SequentialInductionAxioms }
import at.logic.gapt.provers.viper.aip.provers.escargot
import at.logic.gapt.provers.viper.aip.{ AnalyticInductionProver, ProverOptions }

object prop_08 extends TacticsProof {
  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/isaplanner/prop_08.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val baseCaseSequent = sequent.antecedent ++: Sequent() :+
    ( "goal" -> hof"minus(plus(Z, m), plus(Z, n)) = minus(m, n)" )

  val baseCase = Lemma( baseCaseSequent ) {
    allL( "h1", le"m:Nat" )
    allL( "h1", le"n:Nat" )
    forget( "h0", "h1", "h2", "h3", "h4", "h5", "h6" );
    eql( "h1_0", "goal" ).fromLeftToRight
    eql( "h1_1", "goal" ).fromLeftToRight
    refl
  }

  val inductiveCaseSequent = sequent.antecedent ++:
    ( "IHk_0" -> hof"minus(plus(k_0, m), plus(k_0, n)) = minus(m, n)" ) +: Sequent() :+
    ( "goal" -> hof"minus(plus(S(k_0), m), plus(S(k_0), n)) = minus(m, n)" )

  val inductiveCase = Lemma( inductiveCaseSequent ) {
    allL( "h2", le"k_0:Nat", le"m:Nat" )
    allL( "h2", le"k_0:Nat", le"n:Nat" )
    allL( "h5", le"plus(k_0:Nat,m:Nat):Nat", le"plus(k_0:Nat,n:Nat):Nat" )
    forget( "h0", "h1", "h2", "h3", "h4", "h5", "h6" )
    eql( "h2_0", "goal" )
    eql( "h2_1", "goal" )
    eql( "h5_0", "goal" )
    axiomLog
  }

  val proof1 = Lemma( sequent.antecedent ++: Sequent() :+
    ( "goal" -> hof"minus(plus(k, m), plus(k, n)) = minus(m, n)" ) ) {
    induction( hov"k:Nat" )
    insert( baseCase )
    insert( inductiveCase )
  }

  val aipOptions1 = new ProverOptions( escargot, IndependentInductionAxioms().forVariables( List( hov"k:Nat" ) ).forLabel( "goal" ) )
  val proof2 = new AnalyticInductionProver( aipOptions1 ) lkProof ( sequent ) get

  val aipOptions2 = new ProverOptions( escargot, SequentialInductionAxioms().forVariables( List( hov"k:Nat" ) ).forLabel( "goal" ) )
  val proof3 = new AnalyticInductionProver( aipOptions2 ) lkProof ( sequent ) get
}
