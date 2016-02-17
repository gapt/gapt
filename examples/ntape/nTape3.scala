package at.logic.gapt.examples

import at.logic.gapt.formats.llkNew.loadLLK

/**
 * Version 3 of the higher-order n-Tape proof.
 */
object nTape3 extends nTape {

  override def proofdb() = loadLLK( "examples/ntape/ntape-small.llk" )

  override def root_proof() = "TAPEPROOF"

}
