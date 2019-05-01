package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.expr.ty.TBase
import gapt.proofs.context.update.InductiveType
import gapt.proofs.gaptic._

object prop_46 extends TacticsProof {

  // Sorts
  ctx += TBase( "sk" )
  ctx += TBase( "Any" )

  // Inductive types
  ctx += InductiveType( ty"pair3", hoc"'pair22' :sk>sk>pair3" )
  ctx += hoc"'proj1-pair2' :pair3>sk"
  ctx += hoc"'proj2-pair2' :pair3>sk"

  ctx += InductiveType( ty"pair", hoc"'pair2' :Any>sk>pair" )
  ctx += hoc"'proj1-pair' :pair>Any"
  ctx += hoc"'proj2-pair' :pair>sk"

  ctx += InductiveType( ty"list4", hoc"'nil4' :list4", hoc"'cons4' :sk>list4>list4" )
  ctx += hoc"'head4' :list4>sk"
  ctx += hoc"'tail4' :list4>list4"

  ctx += InductiveType( ty"list3", hoc"'nil3' :list3", hoc"'cons3' :pair3>list3>list3" )
  ctx += hoc"'head3' :list3>pair3"
  ctx += hoc"'tail3' :list3>list3"

  ctx += InductiveType( ty"list2", hoc"'nil2' :list2", hoc"'cons2' :pair>list2>list2" )
  ctx += hoc"'head2' :list2>pair"
  ctx += hoc"'tail2' :list2>list2"

  ctx += InductiveType( ty"list", hoc"'nil' :list", hoc"'cons' :Any>list>list" )
  ctx += hoc"'head' :list>Any"
  ctx += hoc"'tail' :list>list"

  //Function constants
  ctx += hoc"'zip2' :list4>list4>list3"
  ctx += hoc"'zip' :list>list4>list2"

  val sequent =
    hols"""
    def_proj1_pair2: ∀x0 ∀x1 ('proj1-pair2'(pair22(x0:sk, x1:sk): pair3): sk) = x0,
    def_proj2_pair2: ∀x0 ∀x1 ('proj2-pair2'(pair22(x0:sk, x1:sk): pair3): sk) = x1,
    def_proj1_pair: ∀x0 ∀x1 ('proj1-pair'(pair2(x0:Any, x1:sk): pair): Any) = x0,
    def_proj2_pair: ∀x0 ∀x1 ('proj2-pair'(pair2(x0:Any, x1:sk): pair): sk) = x1,
    def_head4: ∀x0 ∀x1 (head4(cons4(x0:sk, x1:list4): list4): sk) = x0,
    def_tail4: ∀x0 ∀x1 (tail4(cons4(x0:sk, x1:list4): list4): list4) = x1,
    def_head3: ∀x0 ∀x1 (head3(cons3(x0:pair3, x1:list3): list3): pair3) = x0,
    def_tail3: ∀x0 ∀x1 (tail3(cons3(x0:pair3, x1:list3): list3): list3) = x1,
    def_head2: ∀x0 ∀x1 (head2(cons2(x0:pair, x1:list2): list2): pair) = x0,
    def_tail2: ∀x0 ∀x1 (tail2(cons2(x0:pair, x1:list2): list2): list2) = x1,
    def_head: ∀x0 ∀x1 (head(cons(x0:Any, x1:list): list): Any) = x0,
    def_tail: ∀x0 ∀x1 (tail(cons(x0:Any, x1:list): list): list) = x1,
    def_zip2_0: ∀y (#c(zip2: list4>list4>list3)(nil4:list4, y:list4): list3) = (nil3:list3),
    def_zip2_1: ∀z   ∀x2   (#c(zip2: list4>list4>list3)(cons4(z:sk, x2:list4): list4, nil4:list4):       list3) =     (nil3:list3),
    def_zip2_2: ∀z   ∀x2   ∀x3   ∀x4   (#c(zip2: list4>list4>list3)(cons4(z:sk, x2:list4): list4, cons4(x3, x4)):       list3) =     (cons3(pair22(z, x3): pair3, #c(zip2: list4>list4>list3)(x2, x4): list3):       list3),
    def_zip_0: ∀y (#c(zip: list>list4>list2)(nil:list, y:list4): list2) = (nil2:list2),
    def_zip_1: ∀z   ∀x2   (#c(zip: list>list4>list2)(cons(z:Any, x2:list): list, nil4:list4): list2) =     (nil2:list2),
    def_zip_2: ∀z   ∀x2   ∀x3   ∀x4   (#c(zip: list>list4>list2)(cons(z:Any, x2:list): list,           cons4(x3:sk, x4:list4): list4):       list2) =     (cons2(pair2(z, x3): pair, #c(zip: list>list4>list2)(x2, x4): list2): list2),
    constr_inj_0: ∀y0 ∀y1 nil4 != cons4(y0:sk, y1:list4),
    constr_inj_1: ∀y0 ∀y1 nil3 != cons3(y0:pair3, y1:list3),
    constr_inj_2: ∀y0 ∀y1 nil2 != cons2(y0:pair, y1:list2),
    constr_inj_3: ∀y0 ∀y1 nil != cons(y0:Any, y1:list)
    :-
    goal: ∀xs (#c(zip: list>list4>list2)(nil:list, xs:list4): list2) = (nil2:list2)
  """

  val proof = Lemma( sequent ) {
    trivial
  }
}
