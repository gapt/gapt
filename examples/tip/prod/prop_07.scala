package at.logic.gapt.examples.tip.prod

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.InductiveType
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.provers.viper.aip.AnalyticInductionProver

object prop_07 extends TacticsProof {

  // Sorts
  ctx += TBase( "sk" )

  // Inductive types
  ctx += InductiveType( ty"list", hoc"'nil' :list", hoc"'cons' :sk>list>list" )
  ctx += InductiveType( ty"Nat", hoc"'Z' :Nat", hoc"'S' :Nat>Nat" )

  //Function constants
  ctx += hoc"'qrev' :list>list>list"
  ctx += hoc"'plus' :Nat>Nat>Nat"
  ctx += hoc"'length' :list>Nat"

  val sequent =
    hols"""
        def_head: ∀x0 ∀x1 (head(cons(x0:sk, x1:list): list): sk) = x0,
        def_tail: ∀x0 ∀x1 (tail(cons(x0:sk, x1:list): list): list) = x1,
        def_p: ∀x0 (p(S(x0:Nat): Nat): Nat) = x0,
        def_qrev_0: ∀y (qrev(nil:list, y:list): list) = y,
        def_qrev_1: ∀z ∀xs ∀y (qrev(cons(z:sk, xs:list): list, y:list): list) = qrev(xs, cons(z, y)),
        def_plus_0: ∀y (plus(#c(Z: Nat), y:Nat): Nat) = y,
        def_plus_1: ∀z ∀y (plus(S(z:Nat): Nat, y:Nat): Nat) = S(plus(z, y)),
        def_length_0: (length(nil:list): Nat) = #c(Z: Nat),
        def_length_1: ∀y ∀xs (length(cons(y:sk, xs:list): list): Nat) = S(length(xs)),
        constr_inj_0: ∀y0 ∀y1 ¬(nil:list) = cons(y0:sk, y1:list),
        constr_inj_1: ∀y0 ¬#c(Z: Nat) = S(y0:Nat)
        :-
        goal: ∀x ∀y (length(qrev(x:list, y:list): list): Nat) = plus(length(x), length(y))
  """

  val lem_1 = (
    ( "ap1" -> hof"∀y plus(Z, y) = y" ) +:
    ( "ap2" -> hof"∀z ∀y plus(S(z), y) = S(plus(z, y))" ) +:
    Sequent() :+ ( "lem_1" -> hof"∀x ∀y plus(x,S(y)) = S(plus(x,y))" ) )

  val lem_1_proof = AnalyticInductionProver.singleInduction( lem_1, hov"x:Nat" )

  val cut_lem = ( "lem_1" -> hof"∀x ∀y plus(x,S(y)) = S(plus(x,y))" ) +: sequent

  val cut_lem_proof = AnalyticInductionProver.singleInduction( cut_lem, hov"x:list" )

  val proof = Lemma( sequent ) {
    cut( "lem_1", hof"∀x ∀y plus(x,S(y)) = S(plus(x,y))" )
    insert( lem_1_proof )
    insert( cut_lem_proof )
  }
}
