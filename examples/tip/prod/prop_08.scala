package gapt.examples.tip.prod

import gapt.expr._
import gapt.proofs.context.update.InductiveType
import gapt.proofs.Sequent
import gapt.proofs.gaptic._
import gapt.provers.viper.aip.AnalyticInductionProver

object prop_08 extends TacticsProof {

  // Sorts
  ctx += TBase( "sk" )

  // Inductive types
  ctx += InductiveType( ty"list", hoc"'nil' :list", hoc"'cons' :sk>list>list" )
  ctx += InductiveType( ty"Nat", hoc"'Z' :Nat", hoc"'S' :Nat>Nat" )

  //Function constants
  ctx += hoc"'drop' :Nat>list>list"

  val sequent =
    hols"""
        def_head: ∀x0 ∀x1 (head(cons(x0:sk, x1:list): list): sk) = x0,
        def_tail: ∀x0 ∀x1 (tail(cons(x0:sk, x1:list): list): list) = x1,
        def_p: ∀x0 (p(S(x0:Nat): Nat): Nat) = x0,
        def_drop_0: ∀y (drop(#c(Z: Nat), y:list): list) = y,
        def_drop_1: ∀z (drop(S(z:Nat): Nat, nil:list): list) = nil,
        def_drop_2: ∀z ∀x2 ∀x3 (drop(S(z:Nat): Nat, cons(x2:sk, x3:list): list): list) = drop(z, x3),
        constr_inj_0: ∀y0 ∀y1 ¬(nil:list) = cons(y0:sk, y1:list),
        constr_inj_1: ∀y0 ¬#c(Z: Nat) = S(y0:Nat)
        :-
        goal: ∀x ∀y ∀z drop(x:Nat, drop(y:Nat, z:list): list) = drop(y, drop(x, z))
  """

  val lemma_ldca = (
    ( "h0" -> hof"∀x0 ∀x1 head(cons(x0, x1)) = x0" ) +:
    ( "h1" -> hof"∀x0 ∀x1 tail(cons(x0, x1)) = x1" ) +:
    Sequent() :+ ( "dca" -> hof"∀xs (xs = nil ∨ xs = cons(head(xs), tail(xs)))" ) )

  val lemma_ldca_proof = AnalyticInductionProver.singleInduction( lemma_ldca, hov"xs:list" )

  val lemma_ndca = (
    ( "h2" -> hof"∀x0 p(S(x0)) = x0" ) +:
    Sequent() :+ ( "dca" -> hof"∀x (x = Z ∨ x = S(p(x)))" ) )

  val lemma_ndca_proof = AnalyticInductionProver.singleInduction( lemma_ndca, hov"x:Nat" )

  val lemma_4 = (
    ( "ndca" -> hof"∀x (x = Z ∨ x = S(p(x)))" ) +:
    ( "ldca" -> hof"∀xs (xs = nil ∨ xs = cons(head(xs), tail(xs)))" ) +:
    ( "ad1" -> hof"∀y drop(Z, y) = y" ) +:
    ( "ad2" -> hof"∀z drop(S(z), nil) = nil" ) +:
    ( "ad3" -> hof"∀z ∀x2 ∀x3 drop(S(z), cons(x2, x3)) = drop(z, x3)" ) +:
    Sequent() :+ ( "lemma_4" -> hof"∀y ∀zs ∀x ∀z drop(S(x), drop(y,cons(z,zs))) = drop(x, drop(y,zs))" ) )

  val lemma_4_proof = AnalyticInductionProver.singleInduction( lemma_4, hov"y:Nat" )

  val proof = Lemma( sequent ) {
    cut( "ndca", hof"∀x (x = Z ∨ x = S(p(x)))" )
    insert( lemma_ndca_proof )
    cut( "ldca", hof"∀xs (xs = nil ∨ xs = cons(head(xs), tail(xs)))" )
    insert( lemma_ldca_proof )
    cut( "lemma_4", hof"∀y ∀zs ∀x ∀z drop(S(x), drop(y,cons(z,zs))) = drop(x, drop(y,zs))" )
    insert( lemma_4_proof )
    allR; induction( hov"x:Nat" ).onAll( escargot.withDeskolemization )
  }
}
