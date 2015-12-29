package at.logic.gapt.testing

import at.logic.gapt.formats.tptp.TptpProofParser
import at.logic.gapt.proofs.sketch.RefutationSketchToRobinson

import scala.io.Source

object testTstpImport extends App {
  val Array( filename ) = args

  val tstpOutput = Source fromFile filename mkString

  if ( !tstpOutput.contains( "CNFRefutation" ) )
    println( "NOT_CNF_REFUTATION" )

  val ( endSequent, sketch ) = TptpProofParser parse tstpOutput
  println( s"SKETCH_SIZE ${sketch.subProofs.size}" )

  val resolution = RefutationSketchToRobinson( sketch ) getOrElse {
    println( "FAIL_SKETCH_CONVERSION" )
    sys exit 1
  }

  println( s"RESOLUTION_SIZE ${resolution.subProofs.size}" )

  println( "OK" )
}