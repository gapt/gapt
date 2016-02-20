package at.logic.gapt.examples

import at.logic.gapt.formats.llkNew.loadLLK

/**
 * Version 3 of the higher-order n-Tape proof.
 */
case class nTape4( size: Int ) extends nTape {
  require( 1 < size && size < 5, "We have only instances 2 to 4." )

  override def proofdb() = loadLLK( s"examples/ntape/tape3-$size.llk" )

  override def root_proof() = "TAPEPROOF"

}
