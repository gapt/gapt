package at.logic.gapt.examples.poset

import at.logic.gapt.cutintro.{ GrammarFindingMethod, CutIntroduction }
import at.logic.gapt.examples.Script
import at.logic.gapt.expr.FOLTerm
import at.logic.gapt.grammars.VectTratGrammar
import at.logic.gapt.grammars.deltatable.deltaTable
import at.logic.gapt.proofs.expansion.{ InstanceTermEncoding, FOLInstanceTermEncoding }

object dtable extends Script {

  val constructedProof = proof.cycleImpliesEqual4
  //  val endSequent = constructedProof.endSequent
  //  val ( termset, encoding ) = FOLInstanceTermEncoding( constructedProof )

  CutIntroduction.compressLKProof( constructedProof, new GrammarFindingMethod {
    def findGrammars( lang: Set[FOLTerm] ): Option[VectTratGrammar] = {
      val dtable = deltaTable.createTable( lang.toSet, Some( 3 ) )

      val ( us, s ) = deltaTable.findGrammarFromDeltaTable( lang.toSet, dtable )

      Some( deltaTable.grammarToVTRATG( us, s ) )
    }

    def name = "3_dtable"
  }, verbose = true )

}
