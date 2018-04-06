package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.proofs.Context.InductiveType
import gapt.proofs.gaptic._

object prop_45 extends TacticsProof {

  // Sorts
  ctx += TBase( "sk" )
  // Inductive types
  ctx += InductiveType( ty"list2", hoc"'nil2' :list2", hoc"'cons2' :sk>list2>list2" )
  ctx += InductiveType( ty"Pair", hoc"'Pair2' :sk>sk>Pair" )
  ctx += InductiveType( ty"list", hoc"'nil' :list", hoc"'cons' :Pair>list>list" )

  //Function constants
  ctx += hoc"'zip' :list2>list2>list"

  val sequent =
    hols"""
        def_head2: ∀x0 ∀x1 (head2(cons2(x0:sk, x1:list2): list2): sk) = x0,
        def_tail2: ∀x0 ∀x1 (tail2(cons2(x0:sk, x1:list2): list2): list2) = x1,
        def_first: ∀x0 ∀x1 (first(Pair2(x0:sk, x1:sk): Pair): sk) = x0,
        def_second: ∀x0 ∀x1 (second(Pair2(x0:sk, x1:sk): Pair): sk) = x1,
        def_head: ∀x0 ∀x1 (head(cons(x0:Pair, x1:list): list): Pair) = x0,
        def_tail: ∀x0 ∀x1 (tail(cons(x0:Pair, x1:list): list): list) = x1,
        def_zip_0: ∀y (#c(zip: list2>list2>list)(nil2:list2, y:list2): list) = nil,
        def_zip_1: ∀z   ∀x2   (#c(zip: list2>list2>list)(cons2(z:sk, x2:list2): list2, nil2:list2): list) =     nil,
        def_zip_2: ∀z   ∀x2   ∀x3   ∀x4   (#c(zip: list2>list2>list)(cons2(z:sk, x2:list2): list2, cons2(x3, x4)):       list) =     cons(Pair2(z, x3): Pair, #c(zip: list2>list2>list)(x2, x4): list),
        constr_inj_0: ∀y0 ∀y1 ¬(nil2:list2) = cons2(y0:sk, y1:list2),
        constr_inj_1: ∀y0 ∀y1 ¬(nil:list) = cons(y0:Pair, y1:list)
        :-
        goal: ∀x   ∀y   ∀xs   ∀ys   (#c(zip: list2>list2>list)(cons2(x:sk, xs:list2): list2, cons2(y, ys)):       list) =     cons(Pair2(x, y): Pair, #c(zip: list2>list2>list)(xs, ys): list)
  """

  val proof = Lemma( sequent ) {
    escargot
  }
}
