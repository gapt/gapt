package gapt.cli

import gapt.formats.tptp.check._
import gapt.formats.OnDiskInputFile

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
  if !os.exists(path) then {
    Console.err.println(s"file not found: $path")
    sys.exit(1)
    return
  }

  // directory of the input file defines where we resolve file directives
  val fileDirectiveRoot = path / os.up
  val szsStatus = checkProof(OnDiskInputFile(path), fileDirectiveRoot)
  Console.out.println(szsStatus.statusLine)
}
