package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.{ Context, Sequent }
import at.logic.gapt.provers.viper.aip.axioms.{ SequentialInductionAxioms, StandardInductionAxioms }
import cats.syntax.all._

object prop_03 extends TacticsProof {

  ctx += Context.InductiveType( ty"Nat", hoc"Z:Nat", hoc"S:Nat>Nat" )
  ctx += hoc"p:Nat>Nat"

  ctx += Context.InductiveType( ty"list", hoc"nil:list", hoc"cons:Nat>list>list" )
  ctx += hoc"head:list>Nat"
  ctx += hoc"tail:list>list"

  ctx += hoc"le:Nat>Nat>o"
  ctx += hoc"equal:Nat>Nat>o"
  ctx += hoc"append:list>list>list"
  ctx += hoc"count:Nat>list>Nat"

  val sequent =
    hols"""
          def_pred: ∀x p(S(x)) = x,
          def_head: ∀x ∀xs head(cons(x, xs)) = x,
          def_tail: ∀x ∀xs tail(cons(x, xs)) = xs,
          def_le_1: ∀x le(Z, x),
          def_le_2: ∀x ¬le(S(x), Z),
          def_le_3: ∀x ∀y ((le(S(x), S(y)) ⊃ le(x, y)) ∧ (le(x, y) ⊃ le(S(x), S(y)))),
          def_eq_1: equal(Z, Z),
          def_eq_2: ∀x ¬equal(Z, S(x)),
          def_eq_3: ∀x ¬equal(S(x), Z),
          def_eq_4: ∀x ∀y ((equal(S(x), S(y)) ⊃ equal(x, y)) ∧ (equal(x, y) ⊃ equal(S(x), S(y)))),
          def_count_1: ∀x count(x, nil) = Z,
          def_count_2: ∀x ∀y ∀xs (¬equal(x, y) ⊃ (count(x, cons(y, xs))) = count(x, xs)),
          def_count_3: ∀x ∀y ∀xs (equal(x, y) ⊃ (count(x, cons(y, xs))) = S(count(x, xs))),
          def_append_1: ∀xs append(nil, xs) = xs,
          def_append_2: ∀x ∀xs ∀ys append(cons(x, xs), ys) = cons(x, append(xs, ys)),
          ax_nat: ∀x ¬Z = S(x),
          ax_list: ∀x ∀xs ¬nil = cons(x, xs)
          :-
          goal: ∀n ∀xs ∀ys le(count(n, xs), count(n, append(xs, ys)))
        """

  val cutFormula = hof"∀xs ∀ys ∀n le(count(n, xs), count(n, append(xs, ys)))"

  val proofCutFormula = Lemma( sequent.antecedent ++: Sequent() :+ ( "goal" -> cutFormula ) ) {
    allR
    induction( hov"xs:list" )
    allR
    allR
    allL( "def_count_1", le"n:Nat" )
    allL( "def_le_1", le"count(n:Nat, append(nil, ys:list))" )
    eql( "def_count_1_0", "goal" )
    axiomLog
    allR
    allR
    allL( "def_append_2", le"x:Nat", le"xs_0:list", le"ys:list" )
    eql( "def_append_2_0", "goal" )
    allL( "def_count_2", le"n:Nat", le"x:Nat", le"xs_0:list" )
    impL( "def_count_2_0" )
    negR( "def_count_2_0" )
    allL( "def_count_3", le"n:Nat", le"x:Nat", le"xs_0:list" )
    impL( "def_count_3_0" )
    axiomLog
    allL( "def_count_3", le"n:Nat", le"x:Nat", le"append(xs_0:list, ys:list)" )
    impL
    axiomLog
    eql( "def_count_3_0", "goal" )
    eql( "def_count_3_1", "goal" )
    allL( "def_le_3", le"count(n:Nat, xs_0:list)", le"count(n:Nat, append(xs_0:list, ys:list))" )
    allL( "IHxs_0", le"ys:list", le"n:Nat" )
    andL( "def_le_3_0" )
    impL( "def_le_3_0_1" )
    axiomLog
    axiomLog
    allL( "def_count_2", le"n:Nat", le"x:Nat", le"append(xs_0:list, ys:list)" )
    impL( "def_count_2_1" )
    negR
    allL( "def_count_3", le"n:Nat", le"x:Nat", le"xs_0:list" )
    allL( "def_count_3", le"n:Nat", le"x:Nat", le"append(xs_0:list, ys:list)" )
    impL( "def_count_3_0" )
    axiomLog
    impL( "def_count_3_1" )
    axiomLog
    eql( "def_count_3_0", "goal" )
    eql( "def_count_3_1", "goal" )
    allL( "def_le_3", le"count(n:Nat, xs_0:list)", le"count(n:Nat, append(xs_0:list, ys:list))" )
    andL( "def_le_3_0" )
    allL( "IHxs_0", le"ys:list", le"n:Nat" )
    impL( "def_le_3_0_1" )
    axiomLog
    axiomLog
    eql( "def_count_2_0", "goal" )
    eql( "def_count_2_1", "goal" )
    allL( "IHxs_0", le"ys:list", le"n:Nat" )
    axiomLog
  }

  val proof = Lemma( sequent ) {
    cut( "CF", cutFormula )
    insert( proofCutFormula )
    allR
    allR
    allR
    allL( "CF", le"xs:list", le"ys:list", le"n:Nat" )
    axiomLog
  }

  val inductionAxiom = SequentialInductionAxioms()
    .forVariables( List( hov"xs:list" ) )
    .forLabel( "goal" )( sequent )
    .valueOr( e => throw new Exception( e ) ).head.formula

  val proof2 = Lemma( ( "IAxs_0" -> inductionAxiom ) +: sequent ) {
    escargot
  }

  val proof3 = Lemma( sequent ) {
    analyticInduction.withAxioms {
      StandardInductionAxioms()
        .forVariables( hov"xs:list" )
        .forFormula( hof"∀ys ∀n le(count(n, xs), count(n, append(xs, ys)))" )
    }
  }
}
