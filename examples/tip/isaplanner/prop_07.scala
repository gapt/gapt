package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.proofs.context.Context
import gapt.proofs.gaptic._
import gapt.provers.viper.aip.axioms.IndependentInductionAxioms

/* This proof is not a s.i.p because of the subinduction,
 * in the base case of the primary induction.
 */
object prop_07 extends TacticsProof {

  ctx += Context.InductiveType( ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat" )
  ctx += hoc"p:Nat>Nat"
  ctx += hoc"le:Nat>Nat>o"
  ctx += hoc"plus:Nat>Nat>Nat"

  val sequent = hols"""
                         def_pred: ∀x p(S(x)) = x,
                         def_plus_1: ∀y plus(Z, y) = y,
                         def_plus_2: ∀z ∀y plus(S(z), y) = S(plus(z, y)),
                         def_minus_1: ∀y minus(Z, y) = Z,
                         def_minus_2: ∀z minus(S(z), Z) = S(z),
                         def_minus_3: ∀z ∀x2 minus(S(z), S(x2)) = minus(z, x2),
                         ax_nat_1: ∀x ¬Z = S(x)
                         :-
                         goal: ∀n ∀m minus(plus(n, m), n) = m
  """

  val proof = Lemma( sequent ) {
    allR
    induction( hov"n:Nat" )
    // Base case
    allR
    allL( "def_plus_1", le"m:Nat" )
    eql( "def_plus_1_0", "goal" ).fromLeftToRight
    allL( "def_minus_1", le"Z:Nat" )
    induction( hov"m:Nat" )
    //base case
    axiomLog
    //inductive case
    allL( "def_minus_2", le"m_0:Nat" )
    axiomLog

    // Inductive case
    allR
    forget( "def_pred", "def_plus_1", "def_minus_1", "def_minus_2", "ax_nat_1" )
    allL( "IHn_0", le"m:Nat" )
    allL( "def_plus_2", le"n_0:Nat", le"m:Nat" )
    allL( "def_minus_3", le"plus(n_0:Nat, m:Nat):Nat", le"n_0:Nat" )
    forget( "def_plus_2", "def_minus_3" )
    eql( "def_plus_2_0", "goal" )
    eql( "def_minus_3_0", "goal" )
    axiomLog

  }

  val proof2 = Lemma( sequent ) {
    analyticInduction.withAxioms( IndependentInductionAxioms().
      forVariables( List( hov"n:Nat", hov"m:Nat" ) ).
      forLabel( "goal" ) )
  }
}
