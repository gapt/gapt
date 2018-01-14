package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.viper.aip.axioms.SequentialInductionAxioms
import at.logic.gapt.provers.viper.aip.{ AnalyticInductionProver, ProverOptions }

/* This proof is not a s.i.p. */
object prop_24 extends TacticsProof {

  ctx += TBase( "sk" )
  ctx += Context.InductiveType( ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat" )
  ctx += hoc"p:Nat>Nat"
  ctx += hoc"'max2' :Nat>Nat>Nat"

  ctx += hoc"'le' :Nat>Nat>o"
  ctx += hoc"'equal' :Nat>Nat>o"

  val sequent =
    hols"""
      def_p: ∀x p(S(x)) = x,
      def_max2_1: ∀y (max2(#c(Z: Nat), y:Nat): Nat) = y,
      def_max2_2: ∀z (max2(S(z:Nat): Nat, #c(Z: Nat)): Nat) = S(z),
      def_max2_3: ∀z ∀x2 (max2(S(z:Nat): Nat, S(x2)): Nat) = S(max2(z, x2)),
      def_le_1: ∀y le(#c(Z: Nat), y:Nat),
      def_le_2: ∀z ¬le(S(z:Nat): Nat, #c(Z: Nat)),
      def_le_3: ∀z ∀x2 ((le(S(z:Nat): Nat, S(x2)) → le(z, x2)) ∧ (le(z, x2) → le(S(z), S(x2)))),
      def_equal_1: equal(Z, Z),
      def_equal_2: ∀x ¬equal(Z, S(x)),
      def_equal_3: ∀x ¬equal(S(x), Z),
      def_equal_4: ∀x ∀y ((equal(S(x), S(y)) → equal(x, y)) ∧ (equal(x, y) → equal(S(x), S(y)))),
      ax_nat: ∀x ¬Z = S(x)
      :-
      goal: ∀a ∀b ((equal(max2(a:Nat, b:Nat): Nat, a) → le(b, a)) ∧ (le(b, a) → equal(max2(a, b), a)))
    """

  /* This proof uses induction on the goal, and subinductions on some
   * subformulas of the goal. These subinductions do not use their induction
   * hypothesis and are therefore merely case distinctions.
   */
  val proof1 = Lemma( sequent ) {
    allR
    induction( hov"a:Nat" )
    allR
    andR
    allL( "def_max2_1", le"b:Nat" )
    eql( "def_max2_1_0", "goal" ).fromLeftToRight
    induction( hov"b:Nat" )
    impR
    allL( "def_le_1", le"Z" )
    axiomLog
    impR
    allL( "def_equal_3", le"b_0:Nat" )
    negL
    axiomLog
    allL( "def_max2_1", le"b:Nat" )
    eql( "def_max2_1_0", "goal" ).fromLeftToRight
    induction( hov"b:Nat" )
    impR
    axiomLog
    impR
    allL( "def_le_2", le"b_0:Nat" )
    negL
    axiomLog
    allR
    andR
    // In order to continue we need again to do a case distinction
    // on b. It seems preferable to apply induction before decomposing the formula.
    induction( hov"b:Nat" )
    allL( "def_max2_2", le"a_0:Nat" )
    eql( "def_max2_2_0", "goal" ).fromLeftToRight
    impR
    allL( "def_le_1", le"S(a_0:Nat)" )
    axiomLog
    allL( "def_max2_3", le"a_0:Nat", le"b_0:Nat" )
    eql( "def_max2_3_0", "goal" ).fromLeftToRight
    impR
    allL( "def_equal_4", le"max2(a_0:Nat, b_0:Nat):Nat", le"a_0:Nat" )
    andL( "def_equal_4_0" )
    forget( "def_equal_4_0_1" )
    impL( "def_equal_4_0_0" )
    axiomLog
    allL( "def_le_3", le"b_0:Nat", le"a_0:Nat" )
    andL( "def_le_3_0" )
    forget( "def_le_3_0_0" )
    impL( "def_le_3_0_1" )
    allL( "IHa_0", le"b_0:Nat" )
    andL( "IHa_0_0" )
    forget( "IHa_0_0_1" )
    impL( "IHa_0_0_0" )
    axiomLog
    axiomLog
    axiomLog

    induction( hov"b:Nat" )
    impR
    allL( "def_max2_2", le"a_0:Nat" )
    eql( "def_max2_2_0", "goal_1" ).fromLeftToRight
    // Now we need to prove equal(S(a_0),S(a_0)). This reduces via the axioms
    // to equal(a_0, a_0). But proving this requires a separate induction and this
    // cannot be done with the analytical induction provided by the sequential
    // axioms.
    allL( "def_equal_4", le"a_0:Nat", le"a_0:Nat" )
    andL( "def_equal_4_0" )
    forget( "def_equal_4_0_0" )
    impL( "def_equal_4_0_1" )
    forget( "goal_1" )
    induction( hov"a_0:Nat" )
    axiomLog
    allL( "def_equal_4", le"a_1:Nat", le"a_1:Nat" )
    andL( "def_equal_4_1" )
    forget( "def_equal_4_1_0" )
    impL( "def_equal_4_1_1" )
    axiomLog
    axiomLog
    axiomLog
    impR
    allL( "def_le_3", le"b_0:Nat", le"a_0:Nat" )
    andL( "def_le_3_0" )
    forget( "def_le_3_0_1" )
    impL( "def_le_3_0_0" )
    axiomLog
    allL( "def_max2_3", le"a_0:Nat", le"b_0:Nat" )
    eql( "def_max2_3_0", "goal_1" ).fromLeftToRight
    allL( "def_equal_4", le"max2(a_0:Nat, b_0:Nat):Nat", le"a_0:Nat" )
    andL( "def_equal_4_0" )
    forget( "def_equal_4_0_0" )
    allL( "IHa_0", le"b_0:Nat" )
    andL( "IHa_0_0" )
    forget( "IHa_0_0_0" )
    impL( "IHa_0_0_1" )
    axiomLog
    impL( "def_equal_4_0_1" )
    axiomLog
    axiomLog
  }

  val options = new ProverOptions( Escargot, SequentialInductionAxioms().forAllVariables.forLabel( "goal" ) )
  val proof2 = new AnalyticInductionProver( options ) lkProof ( ( "refl" -> hof"!x equal(x,x)" ) +: sequent ) get
}
