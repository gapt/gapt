package gapt.testing

import gapt.proofs.expansion.InstanceTermEncoding
import gapt.formats.prover9.Prover9TermParserLadrStyle._
import gapt.proofs.loadExpansionProof
import ammonite.ops._

object loadAndCompress extends App {
  val Array( methodName, fileName ) = args
  val path = Path( fileName, pwd )

  val method = parseMethod( methodName )

  val termSet =
    if ( path.ext == "termset" ) {
      read.lines( path ).map( parseTerm )
    } else {
      val expansion = loadExpansionProof( path )
      InstanceTermEncoding( expansion )._1
    }

  method findGrammars termSet.toSet match {
    case Some( grammar ) if grammar.size >= termSet.size => sys exit 10
    case Some( grammar ) if !termSet.toSet.subsetOf( grammar.language ) => sys exit 20
    case Some( grammar ) => sys exit 0
    case None => sys exit 10
  }
}
