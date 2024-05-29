package gapt.proofs

import gapt.cutintro.CutIntroduction
import gapt.formats.{InputFile, StringInputFile}
import gapt.formats.leancop.LeanCoPParser
import gapt.formats.tptp.TptpProofParser
import gapt.formats.verit.VeriTParser
import gapt.proofs.expansion.{ExpansionProof, addSymmetry}
import gapt.proofs.resolution.{ResolutionProof, ResolutionToExpansionProof, containsEquationalReasoning, numberOfLogicalInferencesRes, simplifyResolutionProof}
import gapt.proofs.sketch.RefutationSketchToResolution
import gapt.provers.prover9.Prover9Importer
import gapt.utils.Logger
import os._

object loadExpansionProof {
  val logger = Logger("loadExpansionProof")

  def apply(file: InputFile): ExpansionProof = withBackgroundTheory(file)._1

  def withBackgroundTheory(file: InputFile): (ExpansionProof, CutIntroduction.BackgroundTheory) = file.fileName match {
    case fileName if fileName endsWith ".proof_flat" =>
      val Some(expSeq) = VeriTParser.getExpansionProofWithSymmetry(FilePath(fileName)): @unchecked
      ExpansionProof(expSeq) -> CutIntroduction.BackgroundTheory.PureFOL
    case fileName if fileName contains "/leanCoP" =>
      val Some(expSeq) = LeanCoPParser.getExpansionProof(extractFromTSTPCommentsIfNecessary(file)): @unchecked
      val p = ExpansionProof(expSeq)
      p -> CutIntroduction.BackgroundTheory.guess(p.shallow)
    case fileName if fileName contains "/Prover9" =>
      val (resProof, endSequent) = Prover9Importer.robinsonProofWithReconstructedEndSequent(file)
      loadResolutionProof(resProof, endSequent)
    case _ => // try tstp format
      val tstpOutput = file.read

      logger.metric("tstp_is_cnf_ref", tstpOutput contains "CNFRefutation")

      val (endSequent, sketch) = TptpProofParser.parse(StringInputFile(tstpOutput), ignoreStrongQuants = true)
      logger.metric("tstp_sketch_size", sketch.subProofs.size)

      val Right(resProof) = RefutationSketchToResolution(sketch): @unchecked
      loadResolutionProof(resProof, endSequent)
  }

  def extractFromTSTPCommentsIfNecessary(file: InputFile): StringInputFile = {
    val output = file.read
    val lines = output.split("\n")
    if (lines contains "%----ERROR: Could not form TPTP format derivation")
      StringInputFile(lines.toSeq.dropWhile(_ != "%----ORIGINAL SYSTEM OUTPUT").drop(1).takeWhile(!_.startsWith("%-----")).dropRight(1).map { _ substring 2 }.filterNot(_ startsWith "% SZS").filterNot(_ startsWith "\\n% SZS").mkString("", "\n", "\n"))
    else
      StringInputFile(output)
  }

  private def loadResolutionProof(resProof: ResolutionProof, endSequent: HOLSequent) = {
    logger.metric("resinf_input", numberOfLogicalInferencesRes(simplifyResolutionProof(resProof)))
    val backgroundTheory =
      if (containsEquationalReasoning(resProof))
        CutIntroduction.BackgroundTheory.Equality
      else
        CutIntroduction.BackgroundTheory.PureFOL
    val expansionProof = ResolutionToExpansionProof(resProof)
    expansionProof -> backgroundTheory
  }

}
