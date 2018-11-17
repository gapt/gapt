package gapt.examples.tip.prod

import gapt.expr._
import gapt.proofs.context.update.InductiveType
import gapt.proofs.Sequent
import gapt.proofs.gaptic._
import gapt.provers.viper.aip.AnalyticInductionProver

object prop_28 extends TacticsProof {

  // Sorts
  ctx += TBase( "sk" )

  // Inductive types
  ctx += InductiveType( ty"list2", hoc"'nil2' :list2", hoc"'cons2' :sk>list2>list2" )
  ctx += InductiveType( ty"list", hoc"'nil' :list", hoc"'cons' :list2>list>list" )

  //Function constants
  ctx += hoc"'append' :list2>list2>list2"
  ctx += hoc"'rev' :list2>list2"
  ctx += hoc"'qrevflat' :list>list2>list2"
  ctx += hoc"'revflat' :list>list2"

  val sequent =
    hols"""
        def_head2: ∀x0 ∀x1 (head2(cons2(x0:sk, x1:list2): list2): sk) = x0,
        def_tail2: ∀x0 ∀x1 (tail2(cons2(x0:sk, x1:list2): list2): list2) = x1,
        def_head: ∀x0 ∀x1 (head(cons(x0:list2, x1:list): list): list2) = x0,
        def_tail: ∀x0 ∀x1 (tail(cons(x0:list2, x1:list): list): list) = x1,
        def_append_0: ∀y (append(nil2:list2, y:list2): list2) = y,
        def_append_1: ∀z   ∀xs   ∀y   (append(cons2(z:sk, xs:list2): list2, y:list2): list2) =     cons2(z, append(xs, y)),
        def_rev_0: (rev(nil2:list2): list2) = nil2,
        def_rev_1: ∀y   ∀xs   (rev(cons2(y:sk, xs:list2): list2): list2) = append(rev(xs), cons2(y, nil2)),
        def_qrevflat_0: ∀y (qrevflat(nil:list, y:list2): list2) = y,
        def_qrevflat_1: ∀xs   ∀xss   ∀y   (qrevflat(cons(xs:list2, xss:list): list, y:list2): list2) =     qrevflat(xss, append(rev(xs): list2, y)),
        def_revflat_0: (revflat(nil:list): list2) = nil2,
        def_revflat_1: ∀xs   ∀xss   (revflat(cons(xs:list2, xss:list): list): list2) =     append(revflat(xss), rev(xs): list2),
        constr_inj_0: ∀y0 ∀y1 ¬(nil2:list2) = cons2(y0:sk, y1:list2),
        constr_inj_1: ∀y0 ∀y1 ¬(nil:list) = cons(y0:list2, y1:list)
        :-
        goal: ∀x (revflat(x:list): list2) = qrevflat(x, nil2:list2)
  """

  val lemma = (
    ( "" -> hof"∀y append(nil2, y) = y" ) +:
    ( "" -> hof"∀z ∀xs ∀y append(cons2(z, xs), y) = cons2(z, append(xs, y))" ) +:
    Sequent() :+ ( "" -> hof"!xs append(xs,nil2) = xs" ) )

  val lemma_proof = AnalyticInductionProver.singleInduction( lemma, hov"xs:list2" )

  val lemma_22 = (
    ( "" -> hof"∀y append(nil2, y) = y" ) +:
    ( "" -> hof"∀z ∀xs ∀y append(cons2(z, xs), y) = cons2(z, append(xs, y))" ) +:
    Sequent() :+ ( "" -> hof"!xs !ys !zs append(xs, append(ys, zs)) = append(append(xs,ys),zs)" ) )

  val lemma_22_proof = AnalyticInductionProver.singleInduction( lemma_22, hov"xs:list2" )

  val cong_2 = (
    ( "" -> hof"!xs !ys !zs append(xs, append(ys, zs)) = append(append(xs,ys),zs)" ) +:
    ( "" -> hof"revflat(nil) = nil2" ) +:
    ( "" -> hof"∀xs ∀xss revflat(cons(xs, xss)) = append(revflat(xss), rev(xs))" ) +:
    ( "" -> hof"∀y qrevflat(nil, y) = y" ) +:
    ( "" -> hof"∀xs ∀xss ∀y qrevflat(cons(xs, xss), y) = qrevflat(xss, append(rev(xs), y))" ) +:
    ( "" -> hof"∀y append(nil2, y) = y" ) +:
    ( "" -> hof"∀z ∀xs ∀y append(cons2(z, xs), y) = cons2(z, append(xs, y))" ) +:
    Sequent() :+ ( "" -> hof"!xs !ys append(revflat(xs),ys) = qrevflat(xs, ys)" ) )

  val cong_2_proof = AnalyticInductionProver.singleInduction( cong_2, hov"xs:list" )

  val proof = Lemma( sequent ) {
    cut( "lemma", hof"!xs append(xs,nil2) = xs" )
    insert( lemma_proof )
    cut( "lemma_22", hof"!xs !ys !zs append(xs, append(ys, zs)) = append(append(xs,ys),zs)" )
    insert( lemma_22_proof )
    cut( "cong_2", hof"!xs !ys append(revflat(xs),ys) = qrevflat(xs, ys)" )
    insert( cong_2_proof )
    allR; induction( hov"x:list" ); escargot.withDeskolemization.onAllSubGoals
  }
}
