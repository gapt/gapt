package at.logic.gapt.examples

import at.logic.gapt.formats.ClasspathInputFile
import at.logic.gapt.proofs.ceres_omega.AnalysisWithCeresOmega
import at.logic.gapt.formats.llk.loadLLK

/**
 * Version 3 of the higher-order n-Tape proof.
 */
class nTape3 extends AnalysisWithCeresOmega {

  override def proofdb() = loadLLK( ClasspathInputFile( "ntape/ntape3.llk" ) )

  override def root_proof() = "TAPEPROOF"

  override def printStatistics() = {
    super.printStatistics()
    nTapeInstances.printInstances( this.expansion_proof, this.proofdb.Definitions )
  }

}

object nTape3 extends nTape3