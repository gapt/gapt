package at.logic.gapt.examples.tip.prod

import at.logic.gapt.expr._
import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.gaptic._
import at.logic.gapt.proofs.{ Ant, Sequent }

object prop_04 extends TacticsProof {

  val bench = def_prop_04.loadProblem
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val theory = sequent.antecedent ++: Sequent()

  val lem_2 = hof"!xs!zs!y length(append(xs,cons(y,zs))) = S(length(append(xs,zs)))"

  val lem_2_proof = Lemma( theory :+ ( "l2" -> lem_2 ) ) {
    allR; induction( hov"xs:list" )
    //- BC
    allR; allR
    rewrite.many ltr "h7" in "l2"
    rewrite.many ltr "h4" in "l2"
    refl
    //- IC
    allR; allR
    rewrite.many ltr "h8" in "l2"
    rewrite.many ltr "h4" in "l2"
    rewrite.many ltr "IHxs_0" in "l2"
    refl
  }

  val proof = Lemma( sequent ) {
    cut( "lemma", lem_2 )
    insert( lem_2_proof )
    allR; induction( hov"x:list" )
    //- BC
    rewrite ltr "h7" in "goal"
    rewrite.many ltr "h3" in "goal"
    rewrite ltr "h5" in "goal"
    refl
    //- IC
    rewrite ltr "lemma" in "goal"
    rewrite ltr "h8" in "goal"
    rewrite.many ltr "h4" in "goal"
    rewrite ltr "h6" in "goal"
    rewrite ltr "IHx_0" in "goal"
    refl
  }
}
