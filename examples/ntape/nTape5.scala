package at.logic.gapt.examples

import at.logic.gapt.formats.llkNew.loadLLK

/**
 * Version 3 of the higher-order n-Tape proof.
 */
class nTape5( _size: Int ) extends nTape4( _size ) {
  override def proofdb() = loadLLK( getClass.getClassLoader getResourceAsStream s"ntape/ntape5-$size.llk" )
}
object nTape5 {
  def apply( size: Int ) = new nTape5( size )
}

object nTape5Arith extends nTape4( 2 ) {
  override def proofdb() = loadLLK( getClass.getClassLoader getResourceAsStream s"ntape/ntape5-${size}-arithmetic-ite.llk" )
}