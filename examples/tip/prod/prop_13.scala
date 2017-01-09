package at.logic.gapt.examples.tip.prod

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.gaptic.{ Lemma, TacticsProof, _ }
import at.logic.gapt.proofs.{ Ant, Sequent }

object prop_13 extends TacticsProof {

  val bench = TipSmtParser.fixupAndParse( ClasspathInputFile( "tip/prod/prop_13.smt2", getClass ) )
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }
  val theory = sequent.antecedent ++: Sequent()

  val hypothesis = hof"!x(!y plus(x, S(y)) = S(plus(x,y)) & half(plus(x,x)) = x)"

  val hypothesis_proof = Lemma( theory :+ "hyp" -> hypothesis ) {
    allR; induction( hov"x:Nat" )
    //- base case
    andR
    //-- base case: plus_s_comm
    allR
    rewrite.many ltr "h1" in "hyp"
    refl
    //-- base case: goal
    rewrite.many ltr "h1" in "hyp"
    axiomLog
    //- inductive case
    andL; andR
    //-- inductive case: plus_s_comm
    allR
    rewrite.many ltr "h2" in "hyp"
    rewrite.many ltr "IHx_0_0" in "hyp"
    refl
    //-- inductive case: goal
    rewrite.many ltr "h2" in "hyp"
    rewrite.many ltr "IHx_0_0" in "hyp"
    rewrite.many ltr "h5" in "hyp"
    rewrite.many ltr "IHx_0_1" in "hyp"
    refl
  }

  val proof = Lemma( sequent ) {
    cut( "hyp", hypothesis ); insert( hypothesis_proof )
    escargot
  }
}