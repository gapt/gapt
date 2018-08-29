package gapt.examples.tip.prod

import gapt.expr._
import gapt.proofs.context.update.InductiveType
import gapt.proofs.Sequent
import gapt.proofs.gaptic._

object prop_06 extends TacticsProof {

  // Sorts
  ctx += TBase( "sk" )

  // Inductive types
  ctx += InductiveType( ty"list", hoc"'nil' :list", hoc"'cons' :sk>list>list" )
  ctx += InductiveType( ty"Nat", hoc"'Z' :Nat", hoc"'S' :Nat>Nat" )
  //Constants

  //Function constants
  ctx += hoc"'plus' :Nat>Nat>Nat"
  ctx += hoc"'length' :list>Nat"
  ctx += hoc"'append' :list>list>list"
  ctx += hoc"'rev' :list>list"

  val sequent =
    hols"""
        def_head: ∀x0 ∀x1 (head(cons(x0:sk, x1:list): list): sk) = x0,
        def_tail: ∀x0 ∀x1 (tail(cons(x0:sk, x1:list): list): list) = x1,
        def_p: ∀x0 (p(S(x0:Nat): Nat): Nat) = x0,
        def_plus_0: ∀y (plus(#c(Z: Nat), y:Nat): Nat) = y,
        def_plus_1: ∀z ∀y (plus(S(z:Nat): Nat, y:Nat): Nat) = S(plus(z, y)),
        def_length_0: (length(nil:list): Nat) = #c(Z: Nat),
        def_length_1: ∀y ∀xs (length(cons(y:sk, xs:list): list): Nat) = S(length(xs)),
        def_append_0: ∀y (append(nil:list, y:list): list) = y,
        def_append_1: ∀z   ∀xs   ∀y   (append(cons(z:sk, xs:list): list, y:list): list) = cons(z, append(xs, y)),
        def_rev_0: (rev(nil:list): list) = nil,
        def_rev_1: ∀y ∀xs (rev(cons(y:sk, xs:list): list): list) = append(rev(xs), cons(y, nil)),
        constr_inj_0: ∀y0 ∀y1 ¬(nil:list) = cons(y0:sk, y1:list),
        constr_inj_1: ∀y0 ¬#c(Z: Nat) = S(y0:Nat)
        :-
        goal: ∀x   ∀y   (length(rev(append(x:list, y:list): list): list): Nat) =     plus(length(x), length(y))
  """

  val theory = sequent.antecedent ++: Sequent()

  val lem_2 = (
    ( "al1" -> hof"length(nil) = Z" ) +:
    ( "al2" -> hof"∀y ∀xs length(cons(y, xs)) = S(length(xs))" ) +:
    ( "aa1" -> hof"∀y append(nil, y) = y" ) +:
    ( "aa2" -> hof"∀z ∀xs ∀y append(cons(z, xs), y) = cons(z, append(xs, y))" ) +:
    Sequent() :+ ( "append_left_cons" -> hof"∀xs∀y∀zs length(append(xs,cons(y,zs))) = S(length(append(xs,zs)))" ) )

  val lem_2_proof = Lemma( lem_2 ) {
    allR; induction( hov"xs:list" )
    //- BC
    decompose
    rewrite.many ltr "aa1" in "append_left_cons"
    rewrite.many ltr "al2" in "append_left_cons"
    refl
    //- IC
    decompose
    rewrite.many ltr "aa2" in "append_left_cons"
    rewrite.many ltr "al2" in "append_left_cons"
    rewrite.many ltr "IHxs_0" in "append_left_cons"
    refl
  }

  val lem_3 = (
    ( "al2" -> hof"∀y ∀xs length(cons(y, xs)) = S(length(xs))" ) +:
    ( "al1" -> hof"length(nil) = Z" ) +:
    ( "aa1" -> hof"∀y append(nil, y) = y" ) +:
    ( "aa2" -> hof"∀z ∀xs ∀y append(cons(z, xs), y) = cons(z, append(xs, y))" ) +:
    Sequent() :+ ( "append_one" -> hof"!xs!y length(append(xs,cons(y,nil))) = S(length(xs))" ) )

  val lem_3_proof = Lemma( lem_3 ) {
    cut( "lem_2", hof"∀xs∀y∀zs length(append(xs,cons(y,zs))) = S(length(append(xs,zs)))" )
    insert( lem_2_proof )
    decompose
    rewrite ltr "lem_2" in "append_one"
    induction( hov"xs:list" )
    //- BC
    rewrite ltr "aa1" in "append_one"
    rewrite.many ltr "al1" in "append_one"
    refl
    //- IC
    rewrite ltr "aa2" in "append_one"
    rewrite.many ltr "al2" in "append_one"
    rewrite ltr "IHxs_0" in "append_one"
    refl
  }

  val prop_05 = (
    ( "al1" -> hof"length(nil) = Z" ) +:
    ( "al2" -> hof"∀y ∀xs length(cons(y, xs)) = S(length(xs))" ) +:
    ( "aa1" -> hof"∀y append(nil, y) = y" ) +:
    ( "aa2" -> hof"∀z ∀xs ∀y append(cons(z, xs), y) = cons(z, append(xs, y))" ) +:
    ( "ar1" -> hof"rev(nil) = nil" ) +:
    ( "ar2" -> hof"∀y ∀xs rev(cons(y, xs)) = append(rev(xs), cons(y, nil))" ) +:
    Sequent() :+ ( "length_rev_inv" -> hof"∀x length(rev(x)) = length(x)" ) )

  val prop_05_proof = Lemma( prop_05 ) {
    cut( "lem_3", hof"!xs!y length(append(xs,cons(y,nil))) = S(length(xs))" )
    insert( lem_3_proof )
    allR; induction( hov"x:list" )
    //- BC
    rewrite ltr "ar1" in "length_rev_inv"
    refl
    //- IC
    rewrite ltr "ar2" in "length_rev_inv"
    rewrite ltr "lem_3" in "length_rev_inv"
    rewrite ltr "al2" in "length_rev_inv"
    rewrite ltr "IHx_0" in "length_rev_inv"
    refl
  }

  val proof = Lemma( sequent ) {
    allR; induction( hov"x:list" )
    //- BC
    allR
    rewrite ltr "def_append_0" in "goal"
    rewrite ltr "def_length_0" in "goal"
    rewrite ltr "def_plus_0" in "goal"
    cut( "prop_05", hof"∀x length(rev(x)) = length(x)" )
    insert( prop_05_proof )
    rewrite ltr "prop_05" in "goal"
    refl
    //- IC
    decompose
    rewrite ltr "def_append_1" in "goal"
    rewrite ltr "def_rev_1" in "goal"
    rewrite ltr "def_length_1" in "goal"
    rewrite ltr "def_plus_1" in "goal"
    cut( "lem_3", hof"!xs!y length(append(xs,cons(y,nil))) = S(length(xs))" )
    insert( lem_3_proof )
    rewrite ltr "lem_3" in "goal"
    rewrite ltr "IHx_0" in "goal"
    refl
  }
}
