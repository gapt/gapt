package gapt.examples.tip.prod

import gapt.expr._
import gapt.expr.ty.TBase
import gapt.proofs.context.update.InductiveType
import gapt.proofs.Sequent
import gapt.proofs.gaptic.{Lemma, TacticsProof, _}

object prop_32 extends TacticsProof {

  // Sorts
  ctx += TBase("sk")

  // Inductive types
  ctx += InductiveType(ty"list", hoc"'nil' :list", hoc"'cons' :sk>list>list")
  ctx += InductiveType(ty"Nat", hoc"'Z' :Nat", hoc"'S' :Nat>Nat")

  // Function constants
  ctx += hoc"'length' :list>Nat"
  ctx += hoc"'append' :list>list>list"
  ctx += hoc"'rotate' :Nat>list>list"

  val sequent =
    hols"""
        def_head: ∀x0 ∀x1 (head(cons(x0:sk, x1:list): list): sk) = x0,
        def_tail: ∀x0 ∀x1 (tail(cons(x0:sk, x1:list): list): list) = x1,
        def_p: ∀x0 (p(S(x0:Nat): Nat): Nat) = x0,
        def_length_0: (length(nil:list): Nat) = #c(Z: Nat),
        def_length_1: ∀y ∀xs (length(cons(y:sk, xs:list): list): Nat) = S(length(xs)),
        def_append_0: ∀y (append(nil:list, y:list): list) = y,
        def_append_1: ∀z   ∀xs   ∀y   (append(cons(z:sk, xs:list): list, y:list): list) = cons(z, append(xs, y)),
        def_rotate_0: ∀y (rotate(#c(Z: Nat), y:list): list) = y,
        def_rotate_1: ∀z (rotate(S(z:Nat): Nat, nil:list): list) = nil,
        def_rotate_2: ∀z   ∀x2   ∀x3   (rotate(S(z:Nat): Nat, cons(x2:sk, x3:list): list): list) =     rotate(z, append(x3, cons(x2, nil))),
        constr_inj_0: ∀y0 ∀y1 ¬(nil:list) = cons(y0:sk, y1:list),
        constr_inj_1: ∀y0 ¬#c(Z: Nat) = S(y0:Nat)
        :-
        goal: ∀x (rotate(length(x:list): Nat, x): list) = x
  """

  val theory = sequent.antecedent ++: Sequent()

  val append_nil_left_id = hof"!xs append(xs,nil) = xs"
  val append_nil_left_id_proof = Lemma(theory :+
    ("append_nil_left_id" -> append_nil_left_id)) {
    allR; induction(hov"xs:list")
    // - BC
    rewrite.many ltr "def_append_0" in "append_nil_left_id"; refl
    // - IC
    rewrite.many ltr "def_append_1" in "append_nil_left_id";
    rewrite.many ltr "IHxs_0" in "append_nil_left_id"; refl
  }

  val append_comm = hof"!xs!ys!zs append(xs,append(ys,zs)) = append(append(xs,ys),zs)"
  val append_comm_proof = Lemma(theory :+
    ("append_comm" -> append_comm)) {
    allR; induction(hov"xs:list")
    // - BC
    allR; allR;
    rewrite.many ltr "def_append_0" in "append_comm"; refl
    // - IC
    allR; allR;
    rewrite.many ltr "def_append_1" in "append_comm"
    rewrite.many ltr "IHxs_0" in "append_comm"; refl
  }

  val rot_gen = (append_nil_left_id & append_comm) -->
    hof"!xs!ys rotate(length(xs), append(xs,ys)) = append(ys, xs)"

  val rot_gen_proof = Lemma(theory :+ ("rot_gen" -> rot_gen)) {
    impR; andL; allR; induction(hov"xs:list")
    // - BC
    escargot
    // - IC
    allR
    rewrite.many ltr "def_length_1" in "rot_gen_1"
    rewrite.many ltr "def_append_1" in "rot_gen_1"
    escargot
  }

  val lemma = append_nil_left_id & append_comm & rot_gen

  val lemma_proof = Lemma(theory :+ ("lemma" -> lemma)) {
    andR; andR;
    insert(append_nil_left_id_proof)
    insert(append_comm_proof)
    insert(rot_gen_proof)
  }

  val proof = Lemma(sequent) {
    cut("lemma", lemma)
    insert(lemma_proof)
    escargot
  }
}
