package at.logic.gapt.examples.tip.prod

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.InductiveType
import at.logic.gapt.proofs.Sequent
import at.logic.gapt.proofs.gaptic._

object prop_05 extends TacticsProof {

  // Sorts
  ctx += TBase( "sk" )

  // Inductive types
  ctx += InductiveType( ty"list", hoc"'nil' :list", hoc"'cons' :sk>list>list" )
  ctx += InductiveType( ty"Nat", hoc"'Z' :Nat", hoc"'S' :Nat>Nat" )

  //Function constants
  ctx += hoc"'length' :list>Nat"
  ctx += hoc"'append' :list>list>list"
  ctx += hoc"'rev' :list>list"

  val sequent =
    hols"""
        def_head: ∀x0 ∀x1 (head(cons(x0:sk, x1:list): list): sk) = x0,
        def_tail: ∀x0 ∀x1 (tail(cons(x0:sk, x1:list): list): list) = x1,
        def_p: ∀x0 (p(S(x0:Nat): Nat): Nat) = x0,
        def_length_0: (length(nil:list): Nat) = #c(Z: Nat),
        def_length_1: ∀y ∀xs (length(cons(y:sk, xs:list): list): Nat) = S(length(xs)),
        def_append_0: ∀y (append(nil:list, y:list): list) = y,
        def_append_1: ∀z   ∀xs   ∀y   (append(cons(z:sk, xs:list): list, y:list): list) = cons(z, append(xs, y)),
        def_rev_0: (rev(nil:list): list) = nil,
        def_rev_1: ∀y ∀xs (rev(cons(y:sk, xs:list): list): list) = append(rev(xs), cons(y, nil)),
        constr_inj_0: ∀y0 ∀y1 ¬(nil:list) = cons(y0:sk, y1:list),
        constr_inj_1: ∀y0 ¬#c(Z: Nat) = S(y0:Nat)
        :-
        goal: ∀x (length(rev(x:list): list): Nat) = length(x)
  """

  val lem_3 = (
    ( "al2" -> hof"∀y ∀xs length(cons(y, xs)) = S(length(xs))" ) +:
    ( "al1" -> hof"length(nil) = Z" ) +:
    ( "aa1" -> hof"∀y append(nil, y) = y" ) +:
    ( "aa2" -> hof"∀z ∀xs ∀y append(cons(z, xs), y) = cons(z, append(xs, y))" ) +:
    Sequent() :+ ( "append_one" -> hof"!xs!y length(append(xs,cons(y,nil))) = S(length(xs))" ) )

  val lem_3_proof = Lemma( lem_3 ) {
    allR; induction( hov"xs:list" )
    //- BC
    allR
    rewrite ltr "aa1" in "append_one"
    rewrite ltr "al2" in "append_one"
    rewrite.many ltr "al1" in "append_one"
    refl
    //- IC
    allR
    rewrite ltr "aa2" in "append_one"
    rewrite.many ltr "al2" in "append_one"
    rewrite ltr "IHxs_0" in "append_one"
    refl
  }

  val proof = Lemma( sequent ) {
    cut( "lem_3", hof"!xs!y length(append(xs,cons(y,nil))) = S(length(xs))" )
    insert( lem_3_proof )
    allR; induction( hov"x:list" )
    //- BC
    rewrite ltr "def_rev_0" in "goal"
    rewrite.many ltr "def_length_0" in "goal"
    refl
    //- IC
    rewrite ltr "def_rev_1" in "goal"
    rewrite ltr "lem_3" in "goal"
    rewrite ltr "def_length_1" in "goal"
    rewrite ltr "IHx_0" in "goal"
    refl
  }
}
