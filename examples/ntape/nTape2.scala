package at.logic.gapt.examples

import at.logic.gapt.formats.llkNew.loadLLK

/**
 * Version 2 of the higher-order n-Tape proof.
 */
object nTape2 extends nTape {

  override def proofdb() = loadLLK( "examples/ntape/ntape.llk" )

  override def root_proof() = "TAPEPROOF"

}
