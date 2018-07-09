package gapt.testing

import ammonite.ops.FilePath
import gapt.proofs.expansion.numberOfInstancesET
import gapt.proofs.loadExpansionProof
import gapt.utils.{ LogHandler, verbose }

object testTstpImport extends App {
  val Array( filename ) = args
  verbose {
    val exp = loadExpansionProof( FilePath( filename ) )
    println( s"num_insts = ${numberOfInstancesET( exp )}" )
    println( "OK" )
  }
}