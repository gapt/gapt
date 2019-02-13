package gapt.examples.tip.prod

import gapt.expr._
import gapt.expr.ty.TBase
import gapt.proofs.context.update.InductiveType
import gapt.proofs.Sequent
import gapt.proofs.gaptic._
import gapt.provers.viper.aip.AnalyticInductionProver

object prop_10 extends TacticsProof {

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
        goal: ∀x rev(rev(x:list): list) = x
  """

  val lemma_8 = (
    ( "aa1" -> hof"∀y append(nil, y) = y" ) +:
    ( "aa2" -> hof"∀z ∀xs ∀y append(cons(z, xs), y) = cons(z, append(xs, y))" ) +:
    ( "ar1" -> hof"rev(nil) = nil" ) +:
    ( "ar2" -> hof"∀y ∀xs rev(cons(y, xs)) = append(rev(xs), cons(y, nil))" ) +:
    Sequent() :+ ( "lemma_8" -> hof"∀xs ∀x rev(append(xs, cons(x,nil))) = append(cons(x,nil), rev(xs))" ) )

  val lemma_8_proof = AnalyticInductionProver.singleInduction( lemma_8, hov"xs:list" )

  val proof = Lemma( sequent ) {
    cut( "lemma_8", hof"∀xs ∀x rev(append(xs, cons(x,nil))) = append(cons(x,nil), rev(xs))" )
    insert( lemma_8_proof )
    allR; induction( hov"x:list" ); escargot.withDeskolemization.onAllSubGoals
  }

  val lemma_8_openind_proof = Lemma( lemma_8 ) {
    allR; allR; induction( hov"xs:list" )
    escargot //-IB
    escargot //-IC
  }

  val openind = Lemma( sequent ) {
    cut( "lemma_8", hof"∀xs ∀x rev(append(xs, cons(x,nil))) = append(cons(x,nil), rev(xs))" )
    insert( lemma_8_openind_proof )
    allR; induction( hov"x:list" ); escargot.withDeskolemization.onAllSubGoals
  }

}
