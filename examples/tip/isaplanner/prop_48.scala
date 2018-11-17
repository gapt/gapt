package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.proofs.context.update.InductiveType
import gapt.proofs.Sequent
import gapt.proofs.gaptic._
import gapt.proofs.gaptic.tactics.AnalyticInductionTactic._

object prop_48 extends TacticsProof {

  // Inductive types
  ctx += InductiveType( ty"Nat", hoc"'Z' :Nat", hoc"'S' :Nat>Nat" )
  ctx += InductiveType( ty"list", hoc"'nil' :list", hoc"'cons' :Nat>list>list" )

  //Function constants
  ctx += hoc"'null' :list>o"
  ctx += hoc"'last' :list>Nat"
  ctx += hoc"'butlast' :list>list"
  ctx += hoc"'append' :list>list>list"

  val sequent =
    hols"""
        def_p: ∀x0 (p(S(x0:Nat): Nat): Nat) = x0,
        def_head: ∀x0 ∀x1 (head(cons(x0:Nat, x1:list): list): Nat) = x0,
        def_tail: ∀x0 ∀x1 (tail(cons(x0:Nat, x1:list): list): list) = x1,
        def_null_0: null(nil:list): o,
        def_null_1: ∀y ∀z ¬null(cons(y:Nat, z:list): list),
        def_last_0: (last(nil:list): Nat) = #c(Z: Nat),
        def_last_1: ∀y (last(cons(y:Nat, nil:list): list): Nat) = y,
        def_last_2: ∀y   ∀x2   ∀x3   (last(cons(y:Nat, cons(x2:Nat, x3:list): list)): Nat) = last(cons(x2, x3)),
        def_butlast_0: (butlast(nil:list): list) = nil,
        def_butlast_1: ∀y (butlast(cons(y:Nat, nil:list): list): list) = nil,
        def_butlast_2: ∀y   ∀x2   ∀x3   (butlast(cons(y:Nat, cons(x2:Nat, x3:list): list)): list) =     cons(y, butlast(cons(x2, x3))),
        def_append_0: ∀y (append(nil:list, y:list): list) = y,
        def_append_1: ∀z   ∀xs   ∀y   (append(cons(z:Nat, xs:list): list, y:list): list) = cons(z, append(xs, y)),
        constr_inj_0: ∀y0 ¬#c(Z: Nat) = S(y0:Nat),
        constr_inj_1: ∀y0 ∀y1 ¬(nil:list) = cons(y0:Nat, y1:list)
        :-
        goal: ∀xs   (¬null(xs:list) →     (append(butlast(xs): list, cons(last(xs): Nat, nil:list): list): list) = xs)
  """

  val dca_goal = hof"!xs (xs = nil ∨ ?x ?xss xs = cons(x, xss))"
  val dca = Sequent() :+ ( "goal" -> dca_goal )
  val dca_proof = Lemma( dca ) {
    allR; analyticInduction withAxioms standardAxioms.forVariables( hov"xs:list" ).forLabel( "goal" )
  }

  val manualProof = Lemma( ( "dca" -> hof"!xs (xs = nil ∨ ?x ?xss xs = cons(x, xss))" ) +: sequent ) {
    allR; induction( hov"xs:list" )
    //- IB
    impR; negL; axiomLog
    //- IC
    impR; negL;
    allL( "dca", hov"xs_0:list" )
    orL
    //- IC - 1
    eql( "dca_0", "goal_1" ).fromLeftToRight
    rewrite.many ltr "def_butlast_1" in "goal_1"
    rewrite.many ltr "def_last_1" in "goal_1"
    rewrite.many ltr "def_append_0" in "goal_1"; refl
    //- IC - 2
    exL; exL
    rewrite.many ltr "dca_0" in "goal_1"
    rewrite.many ltr "def_butlast_2" in "goal_1"
    rewrite.many ltr "def_last_2" in "goal_1"
    rewrite.many ltr "def_append_1" in "goal_1"; escargot
  }
}
