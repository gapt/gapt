package gapt.examples.tip.isaplanner

import gapt.expr._
import gapt.proofs.Context
import gapt.proofs.gaptic._
import gapt.provers.escargot.Escargot
import gapt.provers.viper.aip.axioms.IndependentInductionAxioms
import gapt.provers.viper.aip.{ AnalyticInductionProver, ProverOptions }

object prop_43 extends TacticsProof {

  ctx += TBase( "sk" )
  ctx += TBase( "fun1" )

  ctx += Context.InductiveType( ty"list", hoc"nil:list", hoc"cons:sk>list>list" )
  ctx += hoc"head:list>sk"
  ctx += hoc"tail:list>list"

  ctx += hoc"'apply1' :fun1>sk>o"
  ctx += hoc"'takeWhile' :fun1>list>list"
  ctx += hoc"'dropWhile' :fun1>list>list"
  ctx += hoc"'append' :list>list>list"

  val sequent =
    hols"""
           def_head: ∀x0 ∀x1 (head(cons(x0:sk, x1:list): list): sk) = x0,
           def_tail: ∀x0 ∀x1 (tail(cons(x0:sk, x1:list): list): list) = x1,
           def_takeWhile_1: ∀x (takeWhile(x:fun1, nil:list): list) = nil,
           def_takeWhile_2: ∀x ∀z ∀xs (¬apply1(x:fun1, z:sk) → (takeWhile(x, cons(z, xs:list): list): list) = nil),
           def_takeWhile_3: ∀x ∀z ∀xs (apply1(x:fun1, z:sk) → (takeWhile(x, cons(z, xs:list): list): list) = cons(z, takeWhile(x, xs))),
           def_dropWhile_1: ∀x (dropWhile(x:fun1, nil:list): list) = nil,
           def_dropWhile_2: ∀x ∀z ∀xs (¬apply1(x:fun1, z:sk) → (dropWhile(x, cons(z, xs:list): list): list) = cons(z, xs)),
           def_dropWhile_3: ∀x ∀z ∀xs (apply1(x:fun1, z:sk) → (dropWhile(x, cons(z, xs:list): list): list) = dropWhile(x, xs)),
           def_append_1: ∀y (append(nil:list, y:list): list) = y,
           def_append_2: ∀z ∀xs ∀y (append(cons(z:sk, xs:list): list, y:list): list) = cons(z, append(xs, y)),
           ax_list: ∀y0 ∀y1 ¬(nil:list) = cons(y0:sk, y1:list)
           :-
           goal: ∀p ∀xs (append(takeWhile(p:fun1, xs:list): list, dropWhile(p, xs): list): list) = xs
      """

  val aipOptions = new ProverOptions( Escargot, IndependentInductionAxioms().forVariables( List( hov"xs:list" ) ).forLabel( "goal" ) )
  val proof1 = new AnalyticInductionProver( aipOptions ) lkProof ( sequent ) get
}
