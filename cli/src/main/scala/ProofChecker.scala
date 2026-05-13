package gapt.cli

import scala.Predef._
import gapt.formats.tptp.statistics.TstpStatistics
import gapt.formats.tptp.statistics.FileData
import gapt.formats.csv.CSVRow
import os.Path
import gapt.formats.tptp.statistics._

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
def checkProof(args: String*): Unit = {
  val input = args match {
    case Seq() => {
      System.err.println(usage)
      sys.exit(1)
      return
    }
    case Seq("--help") => {
      System.out.println(usage)
      sys.exit(0)
      return
    }
    case Seq(file) => file
  }

  val path = os.Path(input, os.pwd)
  val (sketch, proof) = TstpStatistics.loadFile(
    ProofFile(path),
    print_statistics = true
  )

  sketch match {
    case Left(error) => {
      val errorMessage = error match {
        case FileNotFound(f)             => s"file not found: ${f.fileName}"
        case ParsingError(file)          => s"parsing error: ${file.fileName}"
        case MalformedFile(file)         => s"malformed file: ${file.fileName}"
        case StackOverflow(file)         => s"stack overflow when parsing: ${file.fileName}"
        case ReconstructionTimeout(file) => s"reconstruction timeout: ${file.fileName}"
        case _                           => "unknown error"
      }
      Console.err.println(errorMessage)
      sys.exit(1)
      return
    }
    case Right(_) => {}
  }

  val szsStatus = proof match {
    case Left(ReconstructionGaveUp(_)
        | ReconstructionError(_)) => "FailedVerified"
    case Right(_) => "Verified" // TODO: also check that conclusion of resolution proof matches conjecture
    case Left(_)  => "NotVerified"
  }

  println(s"%SZS status $szsStatus")
}
