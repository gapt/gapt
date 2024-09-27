package gapt.examples.tip.prod

import gapt.expr._
import gapt.expr.ty.TBase
import gapt.proofs.context.update.InductiveType
import gapt.proofs.Sequent
import gapt.proofs.gaptic._

object prop_04 extends TacticsProof {

  // Sorts
  ctx += TBase("sk")

  // Inductive types
  ctx += InductiveType(ty"list", hoc"'nil' :list", hoc"'cons' :sk>list>list")
  ctx += InductiveType(ty"Nat", hoc"'Z' :Nat", hoc"'S' :Nat>Nat")

  // Function constants
  ctx += hoc"'length' :list>Nat"
  ctx += hoc"'double' :Nat>Nat"
  ctx += hoc"'append' :list>list>list"

  val sequent =
    hols"""
        def_head: ∀x0 ∀x1 (head(cons(x0:sk, x1:list): list): sk) = x0,
        def_tail: ∀x0 ∀x1 (tail(cons(x0:sk, x1:list): list): list) = x1,
        def_p: ∀x0 (p(S(x0:Nat): Nat): Nat) = x0,
        def_length_0: (length(nil:list): Nat) = #c(Z: Nat),
        def_length_1: ∀y ∀xs (length(cons(y:sk, xs:list): list): Nat) = S(length(xs)),
        def_double_0: (double(#c(Z: Nat)): Nat) = #c(Z: Nat),
        def_double_1: ∀y (double(S(y:Nat): Nat): Nat) = S(S(double(y))),
        def_append_0: ∀y (append(nil:list, y:list): list) = y,
        def_append_1: ∀z   ∀xs   ∀y   (append(cons(z:sk, xs:list): list, y:list): list) = cons(z, append(xs, y)),
        constr_inj_0: ∀y0 ∀y1 ¬(nil:list) = cons(y0:sk, y1:list),
        constr_inj_1: ∀y0 ¬#c(Z: Nat) = S(y0:Nat)
        :-
        goal: ∀x (length(append(x:list, x): list): Nat) = double(length(x))
  """

  val theory = sequent.antecedent ++: Sequent()

  val lem_2 = hof"!xs!zs!y length(append(xs,cons(y,zs))) = S(length(append(xs,zs)))"

  val lem_2_proof = Lemma(theory :+ ("l2" -> lem_2)) {
    allR; induction(hov"xs:list")
    // - BC
    allR; allR
    rewrite.many ltr "def_append_0" in "l2"
    rewrite.many ltr "def_length_1" in "l2"
    refl
    // - IC
    allR; allR
    rewrite.many ltr "def_append_1" in "l2"
    rewrite.many ltr "def_length_1" in "l2"
    rewrite.many ltr "IHxs_0" in "l2"
    refl
  }

  val proof = Lemma(sequent) {
    cut("lemma", lem_2)
    insert(lem_2_proof)
    allR; induction(hov"x:list")
    // - BC
    rewrite ltr "def_append_0" in "goal"
    rewrite.many ltr "def_length_0" in "goal"
    rewrite ltr "def_double_0" in "goal"
    refl
    // - IC
    rewrite ltr "lemma" in "goal"
    rewrite ltr "def_append_1" in "goal"
    rewrite.many ltr "def_length_1" in "goal"
    rewrite ltr "def_double_1" in "goal"
    rewrite ltr "IHx_0" in "goal"
    refl
  }

  val lem_2_proof_openind = Lemma(theory :+ ("l2" -> lem_2)) {
    allR; allR; allR; induction(hov"xs:list")
    // - BC
    rewrite.many ltr "def_append_0" in "l2"
    rewrite.many ltr "def_length_1" in "l2"
    refl
    // - IC
    rewrite.many ltr "def_append_1" in "l2"
    rewrite.many ltr "def_length_1" in "l2"
    rewrite.many ltr "IHxs_0" in "l2"
    refl
  }

  val openind = Lemma(sequent) {
    cut("lemma", lem_2)
    insert(lem_2_proof_openind)
    allR; induction(hov"x:list")
    // - BC
    rewrite ltr "def_append_0" in "goal"
    rewrite.many ltr "def_length_0" in "goal"
    rewrite ltr "def_double_0" in "goal"
    refl
    // - IC
    rewrite ltr "lemma" in "goal"
    rewrite ltr "def_append_1" in "goal"
    rewrite.many ltr "def_length_1" in "goal"
    rewrite ltr "def_double_1" in "goal"
    rewrite ltr "IHx_0" in "goal"
    refl
  }
}
