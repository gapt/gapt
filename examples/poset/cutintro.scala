package gapt.examples.poset

import gapt.cutintro.CutIntroduction
import gapt.examples.Script
import gapt.grammars.DeltaTableMethod
import gapt.proofs.expansion._
import gapt.proofs.lk.transformations.LKToExpansionProof
import gapt.utils.verbose

object cutintro extends Script {

  val constructedProof = eliminateCutsET(LKToExpansionProof(proof.cycleImpliesEqual4))

  verbose {
    CutIntroduction(
      CutIntroduction.InputProof(constructedProof, CutIntroduction.BackgroundTheory.PureFOL),
      method = DeltaTableMethod(singleQuantifier = false, subsumedRowMerging = true, keyLimit = Some(3))
    )
  }

}
