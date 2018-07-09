package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.proofs.Context
import gapt.proofs.gaptic._
import gapt.provers.viper.aip.axioms.SequentialInductionAxioms

object prop_09 extends TacticsProof {

  ctx += Context.InductiveType( ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat" )
  ctx += hoc"p:Nat>Nat"
  ctx += hoc"plus:Nat>Nat>Nat"
  ctx += hoc"minus:Nat>Nat>Nat"

  val sequent = hols"""
                          def_p: ∀x p(S(x)) = x,
                          def_plus_1: ∀x plus(Z, x) = x,
                          def_plus_2: ∀x ∀y plus(S(x), y) = S(plus(x, y)),
                          def_minus_1: ∀x minus(Z, x) = Z,
                          def_minus_2: ∀x minus(S(x), Z) = S(x),
                          def_minus_3: ∀x ∀y minus(S(x), S(y)) = minus(x, y),
                          ax_nat_1: ∀x ¬Z = S(x)
                          :-
                          goal: ∀i ∀j ∀k minus(minus(i, j), k) = minus(i, plus(j, k))
    """

  val proof1 = Lemma( sequent ) {
    allR
    induction( hov"i:Nat" )
    allR
    allR
    allL( "def_minus_1", le"j:Nat" )
    allL( "def_minus_1", le"plus(j:Nat, k:Nat)" )
    allL( "def_minus_1", le"k:Nat" )
    eql( "def_minus_1_0", "goal" ).fromLeftToRight
    eql( "def_minus_1_1", "goal" ).fromLeftToRight
    eql( "def_minus_1_2", "goal" ).fromLeftToRight
    refl

    allR
    induction( hov"j:Nat" )
    allR
    allL( "def_plus_1", le"k:Nat" )
    allL( "def_minus_2", le"i_0:Nat" )
    eql( "def_plus_1_0", "goal" ).fromLeftToRight
    eql( "def_minus_2_0", "goal" ).fromLeftToRight
    refl

    allR
    allL( "def_minus_3", le"i_0:Nat", le"j_0:Nat" )
    allL( "def_plus_2", le"j_0:Nat", le"k:Nat" )
    allL( "def_minus_3", le"i_0:Nat", le"plus(j_0:Nat, k:Nat)" )
    allL( "IHi_0", le"j_0:Nat", le"k:Nat" )
    eql( "def_minus_3_0", "goal" )
    eql( "def_plus_2_0", "goal" )
    eql( "def_minus_3_1", "goal" )
    axiomLog
  }

  val proof2 = Lemma( sequent ) {
    analyticInduction.withAxioms(
      SequentialInductionAxioms().forVariables( List( hov"i:Nat", hov"j:Nat" ) ).forLabel( "goal" ) )
  }

  val proof3 = Lemma( sequent ) {
    analyticInduction.withAxioms( SequentialInductionAxioms().forAllVariables.forLabel( "goal" ) )
  }

  import gapt.proofs.gaptic.tactics.AnalyticInductionTactic.{ independentAxioms, sequentialAxioms }

  val proof4 = Lemma( sequent ) {
    analyticInduction withAxioms
      sequentialAxioms.forAllVariables.forLabel( "goal" )
  }

  val proof5 = Lemma( sequent ) {
    analyticInduction withAxioms
      sequentialAxioms.forAllVariables.forLabel( "goal" ) :/\: independentAxioms.forVariables( hov"i:Nat" )
  }
}
