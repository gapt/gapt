package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.{ Context, Sequent }
import at.logic.gapt.provers.viper.aip.axioms.{ IndependentInductionAxioms, SequentialInductionAxioms }

object prop_08 extends TacticsProof {

  ctx += Context.InductiveType( ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat" )
  ctx += hoc"p:Nat>Nat"
  ctx += TBase( "sk" )
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
                          goal: ∀k ∀m ∀n minus(plus(k, m), plus(k, n)) = minus(m, n)
    """

  val baseCaseSequent = sequent.antecedent ++: Sequent() :+
    ( "goal" -> hof"!m !n minus(plus(Z, m), plus(Z, n)) = minus(m, n)" )

  val baseCase = Lemma( baseCaseSequent ) {
    allR; allR
    allL( "def_plus_1", le"m:Nat" )
    allL( "def_plus_1", le"n:Nat" )
    forget( "def_p", "def_plus_1", "def_plus_2", "def_minus_1", "def_minus_2", "def_minus_3", "ax_nat_1" );
    eql( "def_plus_1_0", "goal" ).fromLeftToRight
    eql( "def_plus_1_1", "goal" ).fromLeftToRight
    refl
  }

  val inductiveCaseSequent = sequent.antecedent ++:
    ( "IHk_0" -> hof"!m !n minus(plus(k_0, m), plus(k_0, n)) = minus(m, n)" ) +: Sequent() :+
    ( "goal" -> hof"!m !n minus(plus(S(k_0), m), plus(S(k_0), n)) = minus(m, n)" )

  val inductiveCase = Lemma( inductiveCaseSequent ) {
    allR; allR
    allL( "IHk_0", hov"m:Nat", hov"n:Nat" )
    allL( "def_plus_2", le"k_0:Nat", le"m:Nat" )
    allL( "def_plus_2", le"k_0:Nat", le"n:Nat" )
    allL( "def_minus_3", le"plus(k_0:Nat,m:Nat):Nat", le"plus(k_0:Nat,n:Nat):Nat" )
    forget( "def_p", "def_plus_1", "def_plus_2", "def_minus_1", "def_minus_2", "def_minus_3", "ax_nat_1" )
    eql( "def_plus_2_0", "goal" )
    eql( "def_plus_2_1", "goal" )
    eql( "def_minus_3_0", "goal" )
    axiomLog
  }

  val proof1 = Lemma( sequent ) {
    allR
    induction( hov"k:Nat" )
    insert( baseCase )
    insert( inductiveCase )
  }

  val proof2 = Lemma( sequent ) {
    analyticInduction.withAxioms( IndependentInductionAxioms().forVariables( List( hov"k:Nat" ) ).forLabel( "goal" ) )
  }

  val proof3 = Lemma( sequent ) {
    analyticInduction.withAxioms( SequentialInductionAxioms().forVariables( List( hov"k:Nat" ) ).forLabel( "goal" ) )
  }
}
