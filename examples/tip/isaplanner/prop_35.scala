package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.{ Context, Sequent }

object prop_35 extends TacticsProof {

  ctx += TBase( "sk" )
  ctx += TBase( "fun1" )
  ctx += Context.InductiveType( ty"list", hoc"nil:list", hoc"cons:sk>list>list" )
  ctx += hoc"head:list>sk"
  ctx += hoc"tail:list>list"
  ctx += hoc"'dropWhile' :fun1>list>list"
  ctx += hoc"'apply1' :fun1>sk>o"
  ctx += hoc"'lam' :fun1"

  val sequent =
    hols"""
          def_head: ∀x0 ∀x1 (head(cons(x0:sk, x1:list): list): sk) = x0,
          def_tail: ∀x0 ∀x1 (tail(cons(x0:sk, x1:list): list): list) = x1,
          def_dropWhile_1: ∀x (dropWhile(x:fun1, nil:list): list) = nil,
          def_dropWhile_2: ∀x ∀z ∀xs (¬apply1(x:fun1, z:sk) ⊃
            (dropWhile(x, cons(z, xs:list): list): list) = cons(z, xs)),
          def_dropWhile_3: ∀x ∀z ∀xs (apply1(x:fun1, z:sk) ⊃
            (dropWhile(x, cons(z, xs:list): list): list) = dropWhile(x, xs)),
          ax_list: ∀y0 ∀y1 ¬(nil:list) = cons(y0:sk, y1:list),
          def_apply1_1: ∀x ((apply1(lam:fun1, x:sk) ⊃ ⊥) ∧ (⊥ ⊃ apply1(lam, x)))
          :-
          goal: ∀xs (dropWhile(lam:fun1, xs:list): list) = xs
        """

  val domainClosureAxiom = hof"xs = nil ∨ xs = cons(head(xs),tail(xs))"

  val proofDca = Lemma(
    sequent.antecedent ++: Sequent() :+ ( "dca" -> domainClosureAxiom ) ) {
      induction( hov"xs:list" )
      orR
      refl
      orR
      forget( "dca_0" )
      allL( "def_head", le"x:sk", le"xs_0:list" )
      allL( "def_tail", le"x:sk", le"xs_0:list" )
      eql( "def_head_0", "dca_1" ).fromLeftToRight
      eql( "def_tail_0", "dca_1" ).fromLeftToRight
      refl

    }

  val proof = Lemma( sequent ) {
    allR
    cut( "dca", domainClosureAxiom )
    forget( "goal" )
    insert( proofDca )
    orL
    eql( "dca", "goal" )
    allL( "def_dropWhile_1", le"lam" )
    axiomLog
    eql( "dca", "goal" )
    allL( "def_apply1_1", le"head(xs:list):sk" )
    allL( "def_dropWhile_2", le"lam", le"head(xs:list):sk", le"tail(xs:list):list" )
    andL( "def_apply1_1_0" )
    impL( "def_dropWhile_2_0" )
    negR
    impL( "def_apply1_1_0_0" )
    axiomLog
    axiomBot
    axiomLog
  }
}
