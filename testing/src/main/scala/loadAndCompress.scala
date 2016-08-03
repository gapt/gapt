package at.logic.gapt.testing

import at.logic.gapt.proofs.expansion.FOLInstanceTermEncoding

import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle._
import at.logic.gapt.proofs.loadExpansionProof

import better.files._

object loadAndCompress extends App {
  val Array( methodName, fileName ) = args

  val method = parseMethod( methodName )

  val termSet =
    if ( fileName endsWith ".termset" ) {
      fileName.toFile.lines.map( parseTerm ).toSet
    } else {
      val expansion = loadExpansionProof( fileName )
      FOLInstanceTermEncoding( expansion )._1
    }

  method findGrammars termSet match {
    case Some( grammar ) if grammar.size >= termSet.size => sys exit 10
    case Some( grammar ) if !termSet.subsetOf( grammar.language ) => sys exit 20
    case Some( grammar ) => sys exit 0
    case None => sys exit 10
  }
}
