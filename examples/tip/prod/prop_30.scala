package gapt.examples.tip.prod

import gapt.expr._
import gapt.proofs.context.Context.InductiveType
import gapt.proofs.Sequent
import gapt.proofs.gaptic._
import gapt.provers.viper.aip.AnalyticInductionProver

object prop_30 extends TacticsProof {

  // Sorts
  ctx += TBase( "sk" )

  // Inductive types
  ctx += InductiveType( ty"list", hoc"'nil' :list", hoc"'cons' :sk>list>list" )

  //Function constants
  ctx += hoc"'append' :list>list>list"
  ctx += hoc"'rev' :list>list"

  val sequent =
    hols"""
        def_head: ∀x0 ∀x1 (head(cons(x0:sk, x1:list): list): sk) = x0,
        def_tail: ∀x0 ∀x1 (tail(cons(x0:sk, x1:list): list): list) = x1,
        def_append_0: ∀y (append(nil:list, y:list): list) = y,
        def_append_1: ∀z   ∀xs   ∀y   (append(cons(z:sk, xs:list): list, y:list): list) = cons(z, append(xs, y)),
        def_rev_0: (rev(nil:list): list) = nil,
        def_rev_1: ∀y ∀xs (rev(cons(y:sk, xs:list): list): list) = append(rev(xs), cons(y, nil)),
        constr_inj_0: ∀y0 ∀y1 ¬(nil:list) = cons(y0:sk, y1:list)
        :-
        goal: ∀x rev(append(rev(x:list): list, nil:list): list) = x
  """

  val dca_goal = hof"!xs (xs = nil ∨ xs = cons(head(xs), tail(xs)))"

  val dca = (
    ( "" -> hof"∀x0 ∀x1 head(cons(x0, x1)) = x0" ) +:
    ( "" -> hof"∀x0 ∀x1 tail(cons(x0, x1)) = x1" ) +:
    Sequent() :+ ( "" -> dca_goal ) )

  val dca_proof = AnalyticInductionProver.singleInduction( dca, hov"xs:list" )

  val lemma_11_goal = hof"!xs !y !zs append(append(xs, cons(y,nil)), zs) = append(xs, cons(y,zs))"

  val lemma_11 = (
    ( "" -> hof"∀y append(nil, y) = y" ) +:
    ( "" -> hof"∀z ∀xs ∀y append(cons(z, xs), y) = cons(z, append(xs, y))" ) +:
    ( "" -> hof"rev(nil) = nil" ) +:
    ( "" -> hof"∀y ∀xs rev(cons(y, xs)) = append(rev(xs), cons(y, nil))" ) +:
    Sequent() :+ ( "" -> lemma_11_goal ) )

  val lemma_11_proof = AnalyticInductionProver.singleInduction( lemma_11, hov"xs:list" )

  val cong_5_goal = hof"!xs !ys rev(append(rev(xs),ys)) = append(rev(ys),xs)"

  val cong_5 = (
    ( "" -> hof"∀y append(nil, y) = y" ) +:
    ( "" -> hof"∀z ∀xs ∀y append(cons(z, xs), y) = cons(z, append(xs, y))" ) +:
    ( "" -> hof"rev(nil) = nil" ) +:
    ( "" -> hof"∀y ∀xs rev(cons(y, xs)) = append(rev(xs), cons(y, nil))" ) +:
    ( "" -> dca_goal ) +:
    ( "" -> lemma_11_goal ) +:
    Sequent() :+ ( "" -> cong_5_goal ) )

  val cong_5_proof = AnalyticInductionProver.singleInduction( cong_5, hov"xs:list" )

  val proof = Lemma( sequent ) {
    cut( "dca", dca_goal ); insert( dca_proof )
    cut( "lemma_11", lemma_11_goal ); insert( lemma_11_proof )
    cut( "cong_5", cong_5_goal ); insert( cong_5_proof )
    escargot
  }

}
