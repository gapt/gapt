package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.proofs.gaptic.{ TacticsProof, _ }
import at.logic.gapt.proofs.{ Context, Sequent }
import at.logic.gapt.provers.viper.{ AnalyticInductionProver, ProverOptions, escargot, independentInductionAxioms, sequentialInductionAxioms }

object isaplanner06 extends TacticsProof {
  ctx += Context.InductiveType( "nat", hoc"0: nat", hoc"s:nat>nat" )
  ctx += hoc"'+': nat>nat>nat"
  ctx += hoc"'-': nat>nat>nat"

  val theory = (
    ( "p0_" -> hof"∀y 0+y = y" )
    +: ( "ps_" -> hof"∀x∀y s(x)+y = s(x+y)" )
    +: ( "m0_" -> hof"∀y 0-y = 0" )
    +: ( "ms0" -> hof"∀x s(x)-0 = s(x)" )
    +: ( "mss" -> hof"∀x∀y s(x)-s(y) = x - y" )
    +: Sequent()
  )

  val baseCase = Lemma( theory :+ ( "goal" -> hof"∀y 0-(0+y) = 0" ) ) {
    allR
    forget( "p0_", "ps_", "ms0", "mss" )
    rewrite.many ltr "m0_"
    refl
  }

  val inductiveCase = Lemma( ( "IHx_0" -> hof"∀y x_0-(x_0+y) = 0" ) +: theory :+
    ( "goal" -> hof"∀y s(x_0)-(s(x_0)+y) = 0" ) ) {
    allR
    allL( "ps_", le"x_0:nat", le"y:nat" )
    allL( "IHx_0", le"y:nat" )
    allL( "mss", le"x_0:nat", le"x_0 + y" )
    forget( "ps_", "IHx_0", "mss", "p0_", "m0_", "ms0" )
    eql( "ps__0", "goal" )
    eql( "IHx_0_0", "goal" )
    eql( "mss_0", "goal" ).fromLeftToRight
    refl
  }

  val proof1 = Lemma( theory :+ ( "goal" -> hof"∀y x-(x+y) = 0" ) ) {
    induction( hov"x:nat" )
    insert( baseCase )
    insert( inductiveCase )
  }

  val target = theory :+ ( "goal" -> hof"∀x ∀y x-(x+y) = 0" )

  val aipOptions1 = new ProverOptions( escargot, independentInductionAxioms )
  val proof2 = new AnalyticInductionProver( aipOptions1 ) lkProof ( target, "goal", List( hov"x:nat" ) )

  val aipOptions2 = new ProverOptions( escargot, sequentialInductionAxioms )
  val proof3 = new AnalyticInductionProver( aipOptions2 ) lkProof ( target, "goal", List( hov"x:nat" ) )
}

