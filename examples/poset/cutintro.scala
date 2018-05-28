package gapt.examples.poset

import gapt.cutintro.CutIntroduction
import gapt.examples.Script
import gapt.expr._
import gapt.grammars.DeltaTableMethod
import gapt.proofs.expansion._
import gapt.proofs.lk.LKToExpansionProof
import gapt.provers.prover9.Prover9
import gapt.provers.sat.Sat4j
import gapt.utils.verbose

object cutintro extends Script {

  val constructedProof = eliminateCutsET( LKToExpansionProof( proof.cycleImpliesEqual4 ) )

  verbose {
    CutIntroduction(
      CutIntroduction.InputProof( constructedProof, CutIntroduction.BackgroundTheory.PureFOL ),
      method = DeltaTableMethod( singleQuantifier = false, subsumedRowMerging = true, keyLimit = Some( 3 ) ) )
  }

}
