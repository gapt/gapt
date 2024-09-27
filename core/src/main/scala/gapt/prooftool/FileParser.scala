package gapt.prooftool

import gapt.formats.ivy.IvyParser
import gapt.formats.ivy.conversion.IvyToResolution
import gapt.expr._
import gapt.formats.llk.{ExtendedProofDatabase, loadLLK}
import gapt.proofs.resolution.ResolutionProof

import os._

class FileParser(main: ProofToolViewer[_]) {

  def ivyFileReader(path: String): Unit = {
    val ivy = IvyToResolution(IvyParser(FilePath(path)))
    resProofs = ("ivy_proof", ivy) :: Nil
  }

  def llkFileReader(filename: String): Unit = {
    resProofs = Nil
    proofdb = loadLLK(FilePath(filename))
  }

  def parseFile(path: String): Unit = {
    val dnLine = sys.props("line.separator") + sys.props("line.separator")
    try {
      if (path.endsWith(".llk")) llkFileReader(path)
      else if (path.endsWith(".ivy")) ivyFileReader(path)
      else main.warningMessage("Can not recognize file extension: " + path.substring(path.lastIndexOf(".")))
    } catch {
      case err: Throwable =>
        main.errorMessage("Could not load file: " + path + "!" + dnLine + main.getExceptionString(err))
    }
  }

  def getProofs = proofdb.proofs

  def getResolutionProofs = resProofs

  private var proofdb = ExtendedProofDatabase(Map(), Map(), Map())
  private var resProofs: List[(String, ResolutionProof)] = Nil
}
