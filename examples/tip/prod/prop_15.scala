package at.logic.gapt.examples.tip.prod

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.gaptic.{ Lemma, TacticsProof, _ }
import at.logic.gapt.proofs.{ Ant, Sequent }

object prop_15 extends TacticsProof {

  val bench = def_prop_15.loadProblem
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }
  val theory = sequent.antecedent ++: Sequent()

  val proof = Lemma( sequent ) {
    cut( "lemma", hof"!x!y plus(x, S(y)) = S(plus(x,y))" );
    //- proof lemma
    forget( "goal" )
    allR; induction( hov"x:Nat" )
    //-- BC lemma
    allR
    rewrite.many ltr "h1" in "lemma"
    refl
    //-- IC lemma
    allR
    rewrite.many ltr "h2" in "lemma"
    rewrite.many ltr "IHx_0" in "lemma"
    refl
    //- proof goal
    allR;
    rewrite.many ltr "lemma" in "goal"
    refl
  }
}