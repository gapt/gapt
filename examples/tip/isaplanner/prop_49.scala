package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.expr.ty.TBase
import gapt.proofs.Sequent
import gapt.proofs.context.update.InductiveType
import gapt.proofs.gaptic._
import gapt.proofs.gaptic.tactics.AnalyticInductionTactic._

object prop_49 extends TacticsProof {

  // Sorts
  ctx += TBase("sk")

  // Inductive types
  ctx += InductiveType(ty"list", hoc"'nil' :list", hoc"'cons' :sk>list>list")

  // Function constants
  ctx += hoc"'butlast' :list>list"
  ctx += hoc"'append' :list>list>list"
  ctx += hoc"'butlastConcat' :list>list>list"

  val sequent =
    hols"""
        def_head: ∀x0 ∀x1 (head(cons(x0:sk, x1:list): list): sk) = x0,
        def_tail: ∀x0 ∀x1 (tail(cons(x0:sk, x1:list): list): list) = x1,
        def_butlast_0: (butlast(nil:list): list) = nil,
        def_butlast_1: ∀y (butlast(cons(y:sk, nil:list): list): list) = nil,
        def_butlast_2: ∀y   ∀x2   ∀x3   (butlast(cons(y:sk, cons(x2:sk, x3:list): list)): list) =     cons(y, butlast(cons(x2, x3))),
        def_append_0: ∀y (append(nil:list, y:list): list) = y,
        def_append_1: ∀z   ∀xs   ∀y   (append(cons(z:sk, xs:list): list, y:list): list) = cons(z, append(xs, y)),
        def_butlastConcat_0: ∀x (butlastConcat(x:list, nil:list): list) = butlast(x),
        def_butlastConcat_1: ∀x   ∀z   ∀x2   (butlastConcat(x:list, cons(z:sk, x2:list): list): list) =     append(x, butlast(cons(z, x2)): list),
        constr_inj_0: ∀y0 ∀y1 ¬(nil:list) = cons(y0:sk, y1:list)
        :-
        goal: ∀xs ∀ys (butlast(append(xs:list, ys:list): list): list) = butlastConcat(xs, ys)
  """

  val list_projector_axioms = Seq(
    "alp1" -> hof"∀x0 ∀x1 head(cons(x0, x1)) = x0",
    "alp2" -> hof"∀x0 ∀x1 tail(cons(x0, x1)) = x1"
  )

  val append_axioms = Seq(
    "ap1" -> hof"∀y append(nil, y) = y",
    "ap2" -> hof"∀z ∀xs ∀y append(cons(z, xs), y) = cons(z, append(xs, y))"
  )
  val butlastconcat_axioms = Seq(
    "ablc1" -> hof"∀x butlastConcat(x, nil) = butlast(x)",
    "ablc2" -> hof"∀x ∀z ∀x2 butlastConcat(x, cons(z, x2)) = append(x, butlast(cons(z, x2)))"
  )

  val butlast_axioms = Seq(
    "abl1" -> hof"∀y butlast(cons(y, nil)) = nil",
    "abl2" -> hof"∀y ∀x2 ∀x3 butlast(cons(y, cons(x2, x3))) = cons(y, butlast(cons(x2, x3)))"
  )

  val list_dca_goal = hof"!xs (xs = nil ∨ xs = cons(head(xs),tail(xs)))"
  val list_dca =
    (
      ("pl0" -> hof"∀x0 ∀x1 head(cons(x0, x1)) = x0") +:
        ("pl1" -> hof"∀x0 ∀x1 tail(cons(x0, x1)) = x1") +:
        Sequent() :+
        "goal" -> list_dca_goal
    )
  val list_dca_proof = Lemma(list_dca) {
    allR; induction(hov"xs:list"); escargot; escargot
  }

  val append_nil_goal = hof"!xs append(xs,nil) = xs"
  val append_nil_proof = Lemma(append_axioms ++:
    Sequent() :+
    ("goal" -> append_nil_goal)) {
    analyticInduction withAxioms sequentialAxioms.forVariables(hov"xs:list").forLabel("goal")
  }

  val butlast_append_nil_goal = hof"!xs !x butlast(append(xs,cons(x,nil))) = xs"
  val butlast_append_nil_proof = Lemma(append_axioms ++: butlast_axioms ++:
    ("dca" -> list_dca_goal) +:
    Sequent() :+
    ("goal" -> butlast_append_nil_goal)) {
    allR; induction(hov"xs:list")
    escargot
    allR
    allL("dca", le"xs_0:list")
    orL
    escargot
    escargot
  }

  val list_domain_closure = hof"xs_0 = nil | ?v ?vs xs_0 = cons(v,vs)"

  val proof_list_domain_closure =
    Lemma(Sequent() :+ ("goal" -> list_domain_closure)) {
      induction(hov"xs_0: list")
      escargot
      escargot
    }

  // simplified proof
  val proof2 = Lemma(sequent) {
    allR;
    allR
    induction(hov"ys:list")
    // IB
    rewrite ltr "def_butlastConcat_0" in "goal"
    analyticInduction withAxioms sequentialAxioms.forVariables(hov"xs:list").forFormula(hof"!xs append(xs,nil) = xs")
    // IS
    rewrite ltr "def_butlastConcat_1" in "goal"
    induction(hov"xs:list")
    // IS - IB
    escargot
    // IS - IS
    cut(
      "list_domain_closure",
      hof"xs_0 = nil | ?v ?vs xs_0 = cons(v,vs)"
    )
    insert(proof_list_domain_closure)
    orL("list_domain_closure")
    // subgoal 1 ( xs_0 = nil )
    rewrite.many ltr "list_domain_closure" in "goal"
    rewrite.many ltr "def_append_0" in "goal"
    escargot
    // subgoal 2 ( ?v ?vs xs_0 = cons(v,vs) )
    exL("list_domain_closure")
    exL("list_domain_closure")
    rewrite ltr "list_domain_closure" in "goal"
    rewrite ltr "def_append_1" in "goal"
    rewrite ltr "def_append_1" in "goal"
    rewrite ltr "def_butlast_2" in "goal"
    rewrite rtl "def_append_1" in "goal"
    rewrite rtl "list_domain_closure" in "goal"
    rewrite ltr "IHxs_0" in "goal"
    rewrite rtl "def_append_1" in "goal"
    refl
  }

  val append_inner_shift_goal = hof"!xs !ys !x append(xs, cons(x,ys)) = append(append(xs,cons(x,nil)),ys)"
  val append_inner_shift_proof = Lemma(append_axioms ++:
    Sequent() :+
    ("goal" -> append_inner_shift_goal)) {
    analyticInduction withAxioms sequentialAxioms.forVariables(hov"xs:list").forLabel("goal")
  }

  val butlast_inner_append_goal = hof"!ys !xs !y butlast(append(xs, cons(y,ys))) = append(xs, butlast(cons(y,ys)))"
  val butlast_inner_append_proof = Lemma(butlast_axioms ++: append_axioms ++:
    ("lem_api" -> append_inner_shift_goal) +:
    ("lem_ban" -> butlast_append_nil_goal) +:
    ("lem_ani" -> append_nil_goal) +:
    Sequent() :+
    ("goal" -> butlast_inner_append_goal)) {
    analyticInduction withAxioms sequentialAxioms.forVariables(hov"ys:list").forLabel("goal")
  }

  val proof = Lemma(sequent) {
    cut("", list_dca_goal); insert(list_dca_proof)
    cut("", append_inner_shift_goal); insert(append_inner_shift_proof)
    cut("append_lemma", append_nil_goal); insert(append_nil_proof)
    cut("", butlast_append_nil_goal); insert(butlast_append_nil_proof)
    cut("main_lemma", butlast_inner_append_goal); insert(butlast_inner_append_proof)
    allR; allR
    induction(hov"ys:list")
    rewrite ltr "def_butlastConcat_0" in "goal"
    rewrite ltr "append_lemma" in "goal"
    refl
    rewrite ltr "def_butlastConcat_1" in "goal"
    rewrite ltr "main_lemma" in "goal"
    refl
  }
}
