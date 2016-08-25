package at.logic.gapt.examples.poset

import at.logic.gapt.cutintro.CutIntroduction
import at.logic.gapt.examples.Script
import at.logic.gapt.expr._
import at.logic.gapt.grammars.DeltaTableMethod
import at.logic.gapt.proofs.expansion._
import at.logic.gapt.proofs.lk.LKToExpansionProof
import at.logic.gapt.provers.prover9.Prover9
import at.logic.gapt.provers.sat.Sat4j

object cutintro extends Script {

  val constructedProof = eliminateCutsET( LKToExpansionProof( proof.cycleImpliesEqual4 ) )

  CutIntroduction.makeVerbose()
  CutIntroduction(
    constructedProof,
    method = DeltaTableMethod( singleQuantifier = false, subsumedRowMerging = true, keyLimit = Some( 3 ) )
  )

}
