package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.expr._
import at.logic.gapt.proofs.Context.InductiveType
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.provers.escargot.Escargot
import at.logic.gapt.provers.viper.aip.axioms.IndependentInductionAxioms
import at.logic.gapt.provers.viper.aip.{ AnalyticInductionProver, ProverOptions }

object prop_44 extends TacticsProof {

  // Sorts
  ctx += TBase( "sk" )

  // Inductive types
  ctx += InductiveType( ty"list2", hoc"'nil2' :list2", hoc"'cons2' :sk>list2>list2" )
  ctx += InductiveType( ty"Pair", hoc"'Pair2' :sk>sk>Pair" )
  ctx += InductiveType( ty"list", hoc"'nil' :list", hoc"'cons' :Pair>list>list" )

  //Function constants
  ctx += hoc"'zip' :list2>list2>list"
  ctx += hoc"'zipConcat' :sk>list2>list2>list"

  val sequent =
    hols"""
      def_head2: ∀x0 ∀x1 (head2(cons2(x0:sk, x1:list2): list2): sk) = x0,
      def_tail2: ∀x0 ∀x1 (tail2(cons2(x0:sk, x1:list2): list2): list2) = x1,
      def_first: ∀x0 ∀x1 (first(Pair2(x0:sk, x1:sk): Pair): sk) = x0,
      def_second: ∀x0 ∀x1 (second(Pair2(x0:sk, x1:sk): Pair): sk) = x1,
      def_head: ∀x0 ∀x1 (head(cons(x0:Pair, x1:list): list): Pair) = x0,
      def_tail: ∀x0 ∀x1 (tail(cons(x0:Pair, x1:list): list): list) = x1,
      def_zip_0: ∀y (#c(zip: list2>list2>list)(nil2:list2, y:list2): list) = nil,
      def_zip_1: ∀z   ∀x2   (#c(zip: list2>list2>list)(cons2(z:sk, x2:list2): list2, nil2:list2): list) =     nil,
      def_zip_2: ∀z   ∀x2   ∀x3   ∀x4   (#c(zip: list2>list2>list)(cons2(z:sk, x2:list2): list2, cons2(x3, x4)):       list) =     cons(Pair2(z, x3): Pair, #c(zip: list2>list2>list)(x2, x4): list),
      def_zipConcat_0: ∀x   ∀y   (#c(zipConcat: sk>list2>list2>list)(x:sk, y:list2, nil2:list2): list) = nil,
      def_zipConcat_1: ∀x   ∀y   ∀y2   ∀ys   (#c(zipConcat: sk>list2>list2>list)(x:sk, y:list2,         cons2(y2:sk, ys:list2): list2):       list) =     cons(Pair2(x, y2): Pair, #c(zip: list2>list2>list)(y, ys): list),
      constr_inj_0: ∀y0 ∀y1 ¬(nil2:list2) = cons2(y0:sk, y1:list2),
      constr_inj_1: ∀y0 ∀y1 ¬(nil:list) = cons(y0:Pair, y1:list)
      :-
      goal: ∀x   ∀xs   ∀ys   (#c(zip: list2>list2>list)(cons2(x:sk, xs:list2): list2, ys:list2): list) =     #c(zipConcat: sk>list2>list2>list)(x, xs, ys)
  """

  val aipOptions = new ProverOptions( Escargot, IndependentInductionAxioms().forVariables( List( hov"ys:list2" ) ).forLabel( "goal" ) )
  val proof1 = new AnalyticInductionProver( aipOptions ) lkProof ( sequent ) get
}
