package gapt.examples.tip.prod

import gapt.expr._
import gapt.proofs.context.update.InductiveType
import gapt.proofs.Sequent
import gapt.proofs.gaptic._
import gapt.provers.viper.aip.AnalyticInductionProver

object prop_07 extends TacticsProof {

  // Sorts
  ctx += TBase( "sk" )

  // Inductive types
  ctx += InductiveType( ty"list", hoc"'nil' :list", hoc"'cons' :sk>list>list" )
  ctx += InductiveType( ty"Nat", hoc"'Z' :Nat", hoc"'S' :Nat>Nat" )

  //Function constants
  ctx += hoc"'qrev' :list>list>list"
  ctx += hoc"'plus' :Nat>Nat>Nat"
  ctx += hoc"'length' :list>Nat"

  val sequent =
    hols"""
        def_head: ∀x0 ∀x1 head(cons(x0, x1)) = x0,
        def_tail: ∀x0 ∀x1 tail(cons(x0, x1)) = x1,
        def_p: ∀x0 p(S(x0)) = x0,
        def_qrev_0: ∀y qrev(nil, y) = y,
        def_qrev_1: ∀z ∀xs ∀y qrev(cons(z, xs), y) = qrev(xs, cons(z, y)),
        def_plus_0: ∀y plus(Z, y) = y,
        def_plus_1: ∀z ∀y plus(S(z), y) = S(plus(z, y)),
        def_length_0: length(nil) = Z,
        def_length_1: ∀y ∀xs length(cons(y, xs)) = S(length(xs)),
        constr_inj_0: ∀y0 ∀y1 ¬nil = cons(y0, y1),
        constr_inj_1: ∀y0 ¬Z = S(y0)
        :-
        goal: ∀x ∀y length(qrev(x, y)) = plus(length(x), length(y))
  """

  val lem_1 = ( "ap1" -> hof"∀y plus(Z, y) = y" ) +:
    ( "ap2" -> hof"∀z ∀y plus(S(z), y) = S(plus(z, y))" ) +:
    Sequent() :+ ( "lem_1" -> hof"∀x ∀y plus(x,S(y)) = S(plus(x,y))" )

  val lem_1_proof = AnalyticInductionProver.singleInduction( lem_1, hov"x:Nat" )

  val cut_lem = ( "lem_1" -> hof"∀x ∀y plus(x,S(y)) = S(plus(x,y))" ) +: sequent

  val cut_lem_proof = AnalyticInductionProver.singleInduction( cut_lem, hov"x:list" )

  val proof = Lemma( sequent ) {
    cut( "lem_1", hof"∀x ∀y plus(x,S(y)) = S(plus(x,y))" )
    insert( lem_1_proof )
    insert( cut_lem_proof )
  }

  val proof2 = Lemma( sequent ) {
    cut( "l", hof"""
        !x!y (length(qrev x y) = plus(length x, length y) &
              plus(length x, S(length y)) = S(plus(length x, length y)))
      """ ) right escrgt
    forget( "goal" ); allR( hov"x:list" )
    induction( hov"x:list" ) onAll escrgt
  }
}
