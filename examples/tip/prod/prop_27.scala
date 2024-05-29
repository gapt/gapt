package gapt.examples.tip.prod

import gapt.expr._
import gapt.expr.ty.TBase
import gapt.proofs.context.update.InductiveType
import gapt.proofs.Sequent
import gapt.proofs.gaptic._
import gapt.provers.viper.aip.AnalyticInductionProver

object prop_27 extends TacticsProof {

  // Sorts
  ctx += TBase("sk")

  // Inductive types
  ctx += InductiveType(ty"list", hoc"'nil' :list", hoc"'cons' :sk>list>list")

  // Function constants
  ctx += hoc"'qrev' :list>list>list"
  ctx += hoc"'append' :list>list>list"
  ctx += hoc"'rev' :list>list"

  val sequent =
    hols"""
        def_head: ∀x0 ∀x1 (head(cons(x0:sk, x1:list): list): sk) = x0,
        def_tail: ∀x0 ∀x1 (tail(cons(x0:sk, x1:list): list): list) = x1,
        def_qrev_0: ∀y (qrev(nil:list, y:list): list) = y,
        def_qrev_1: ∀z ∀xs ∀y (qrev(cons(z:sk, xs:list): list, y:list): list) = qrev(xs, cons(z, y)),
        def_append_0: ∀y (append(nil:list, y:list): list) = y,
        def_append_1: ∀z   ∀xs   ∀y   (append(cons(z:sk, xs:list): list, y:list): list) = cons(z, append(xs, y)),
        def_rev_0: (rev(nil:list): list) = nil,
        def_rev_1: ∀y ∀xs (rev(cons(y:sk, xs:list): list): list) = append(rev(xs), cons(y, nil)),
        constr_inj_0: ∀y0 ∀y1 ¬(nil:list) = cons(y0:sk, y1:list)
        :-
        goal: ∀x (rev(x:list): list) = qrev(x, nil:list)
  """

  val lemma_22 =
    (
      ("" -> hof"∀y append(nil, y) = y") +:
        ("" -> hof"∀z ∀xs ∀y append(cons(z, xs), y) = cons(z, append(xs, y))") +:
        Sequent() :+ ("" -> hof"!xs !ys !zs append(xs, append(ys, zs)) = append(append(xs,ys),zs)")
    )

  val lemma_22_proof = AnalyticInductionProver.singleInduction(lemma_22, hov"xs:list")

  val cong_1 =
    (
      ("" -> hof"∀y qrev(nil, y) = y") +:
        ("" -> hof"∀z ∀xs ∀y qrev(cons(z, xs), y) = qrev(xs, cons(z, y))") +:
        ("" -> hof"rev(nil) = nil") +:
        ("" -> hof"∀y ∀xs rev(cons(y, xs)) = append(rev(xs), cons(y, nil))") +:
        ("" -> hof"∀y append(nil, y) = y") +:
        ("" -> hof"∀z ∀xs ∀y append(cons(z, xs), y) = cons(z, append(xs, y))") +:
        ("" -> hof"!xs !ys !zs append(xs, append(ys, zs)) = append(append(xs,ys),zs)") +:
        Sequent() :+ ("" -> hof"!xs !ys append(rev(xs),ys) = qrev(xs, ys)")
    )

  val cong_1_proof = AnalyticInductionProver.singleInduction(cong_1, hov"xs:list")

  val proof = Lemma(sequent) {
    cut("lemma_22", hof"!xs !ys !zs append(xs, append(ys, zs)) = append(append(xs,ys),zs)")
    insert(lemma_22_proof)
    cut("cong_1", hof"!xs !ys append(rev(xs),ys) = qrev(xs, ys)")
    insert(cong_1_proof)
    allR; induction(hov"x:list"); escargot.withDeskolemization.onAllSubGoals
  }
}
