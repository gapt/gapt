package at.logic.gapt.examples.tip.isaplanner

import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.formats.tip.TipSmtParser
import at.logic.gapt.proofs.Ant
import at.logic.gapt.proofs.gaptic.{ Lemma, TacticsProof }
import at.logic.gapt.prooftool.prooftool
import at.logic.gapt.provers.viper.TreeGrammarInductionTactic
import at.logic.gapt.provers.viper.grammars.TreeGrammarProverOptions

object prop_59 extends TacticsProof {

  val bench = def_prop_59.loadProblem
  ctx = bench.ctx

  val sequent = bench.toSequent.zipWithIndex.map {
    case ( f, Ant( i ) ) => s"h$i" -> f
    case ( f, _ )        => "goal" -> f
  }

  val proof_1 = Lemma( sequent ) {
    new TreeGrammarInductionTactic( TreeGrammarProverOptions().copy( quantTys = Some( Seq() ) ) ).aka( "treegrammar without quantifiers" )
  }
}
