package gapt.testing

import gapt.formats.{InputFile, StdinInputFile}
import gapt.formats.tptp._
import os._
import gapt.proofs.resolution.structuralCNF

object clausifier extends App {
  val input: InputFile = args match {
    case Array(fn) => FilePath(fn)
    case _         => StdinInputFile()
  }
  val tptp = TptpImporter.loadWithIncludes(input)
  val inputClauses = TptpProblemToResolution(tptp)
  val cnf = structuralCNF.onProofs(inputClauses)
  val tptpCNF = TptpFile(for ((cls, i) <- cnf.toSeq.zipWithIndex)
    yield resolutionToTptp.fofOrCnf(s"cls_$i", "axiom", cls, Seq()))
  println(tptpCNF)
}
