package gapt.cli

import gapt.formats.csv.CSVRow
import gapt.formats.tptp.TptpImporter
import gapt.formats.tptp.check._
import gapt.formats.tptp.statistics.FileData
import os.Path

case class ProofFile(path: Path) extends FileData {
  override def fileName: String = path.toString
  override def csvHeader(): CSVRow[String] = CSVRow(List("proof"))
  override def toCSV(): CSVRow[String] = CSVRow(List(path.toString))
}

val usage = """
|check-proof <PROOF>
|
|Checks the correctness of a given proof.
|PROOF is a path to a TSTP proof file""".stripMargin.strip

@main
def checkTstpProof(args: String*): Unit = {
  val input = args match {
    case Seq() => {
      Console.err.println(usage)
      sys.exit(1)
      return
    }
    case Seq("--help") => {
      Console.out.println(usage)
      sys.exit(0)
      return
    }
    case Seq(file) => file
  }

  val path = os.Path(input, os.pwd)
  val tptpFile = TptpImporter.loadWithoutIncludes(ProofFile(path))
  val szsStatus = checkProof(tptpFile)

  println(szsStatus.statusLine)
}
