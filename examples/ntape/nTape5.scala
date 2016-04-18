package at.logic.gapt.examples

import at.logic.gapt.formats.llk.loadLLK

/**
 * Version 5 of the higher-order n-Tape proof, where if-then-else is directly axiomatized i.e. it has 2 additional
 * axioms P -> if code(P) then t else f = t and -P -> if code(P) then t else f = f which were theorems before.
 * In contrast to [[nTape4]] it cuts on instances of the theorem C
 * for specific upper bounds n. Since the instantiated proofs were generated manually, only nTape5(2) to nTape5(4)
 * work.
 */
class nTape5( _size: Int ) extends nTape4( _size ) {
  override def proofdb() = loadLLK( getClass.getClassLoader getResourceAsStream s"ntape/ntape5-$size.llk" )
}

/**
 * Version 5 of the higher-order n-Tape proof. In contrast to [[nTape4]] it cuts on instances of the theorem C
 * for specific upper bounds n. Since the instantiated proofs were generated manually, only nTape5(2) to nTape5(4)
 * work.
 */
object nTape5 {
  lazy val inst2 = new nTape5( 2 )
  lazy val inst3 = new nTape5( 3 )
  lazy val inst4 = new nTape5( 4 )

  def apply( size: Int ) = size match {
    case 2 => inst2
    case 3 => inst3
    case 4 => inst4
    case _ => throw new Exception( "We have only instances 2 to 4." )
  }
}

/**
 * Version 5 of the higher-order n-Tape proof, where if-then-else is still proved in arithmetic.
 * In contrast to [[nTape4]] it cuts on instances of the theorem C
 * for specific upper bounds n. Since the instantiated proofs were generated manually, only nTape5Arith(2) works.
 */
class nTape5Arith( _size: Int ) extends nTape4( _size ) {
  override def proofdb() = loadLLK( getClass.getClassLoader getResourceAsStream s"ntape/ntape5-${size}-arithmetic-ite.llk" )
}

/**
 * Version 5 of the higher-order n-Tape proof, where if-then-else is still proved in arithmetic.
 * In contrast to [[nTape4]] it cuts on instances of the theorem C
 * for specific upper bounds n. Since the instantiated proofs were generated manually, only nTape5Arith(2) works.
 */
object nTape5Arith {
  lazy val inst2 = new nTape5Arith( 2 )

  def apply( size: Int ) = size match {
    case 2 => inst2
    case _ => throw new Exception( "We have only instance 2." )
  }
}