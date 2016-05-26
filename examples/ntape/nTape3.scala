package at.logic.gapt.examples

import at.logic.gapt.proofs.ceres_omega.AnalysisWithCeresOmega
import at.logic.gapt.formats.llk.loadLLK

/**
 * Version 3 of the higher-order n-Tape proof.
 */
object nTape3 extends AnalysisWithCeresOmega {

  override def proofdb() = loadLLK( getClass.getClassLoader getResourceAsStream "ntape/ntape3.llk" )

  override def root_proof() = "TAPEPROOF"

  override def printStatistics() = {
    super.printStatistics()
    nTapeInstances.printInstances( this.expansion_proof, this.proofdb.Definitions )
  }

}
