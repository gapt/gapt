package at.logic.gapt.testing

import at.logic.gapt.formats.StringInputFile
import at.logic.gapt.formats.tptp.TptpProofParser
import at.logic.gapt.proofs.sketch.RefutationSketchToResolution

import better.files._

object testTstpImport extends App {
  val Array( filename ) = args

  val tstpOutput = filename.toFile.contentAsString

  if ( !tstpOutput.contains( "CNFRefutation" ) )
    println( "NOT_CNF_REFUTATION" )

  val ( endSequent, sketch ) = TptpProofParser parse StringInputFile( tstpOutput )
  println( s"SKETCH_SIZE ${sketch.subProofs.size}" )

  val resolution = RefutationSketchToResolution( sketch ) getOrElse {
    println( "FAIL_SKETCH_CONVERSION" )
    sys exit 1
  }

  println( s"RESOLUTION_SIZE ${resolution.subProofs.size}" )

  println( "OK" )
}