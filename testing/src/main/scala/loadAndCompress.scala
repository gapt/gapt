package at.logic.gapt.testing

import at.logic.gapt.proofs.expansion.FOLInstanceTermEncoding

import scala.io.Source
import at.logic.gapt.formats.prover9.Prover9TermParserLadrStyle._
import at.logic.gapt.proofs.loadExpansionProof

object loadAndCompress extends App {
  val Array( methodName, fileName ) = args

  val method = parseMethod( methodName )

  val termSet =
    if ( fileName endsWith ".termset" ) {
      Source.fromFile( fileName ).getLines().map( parseTerm ).toSet
    } else {
      val Some( ( expansion, _ ) ) = loadExpansionProof( fileName )
      FOLInstanceTermEncoding( expansion )._1
    }

  method findGrammars termSet match {
    case Some( grammar ) if grammar.size >= termSet.size => sys exit 10
    case Some( grammar ) if !termSet.subsetOf( grammar.language ) => sys exit 20
    case Some( grammar ) => sys exit 0
    case None => sys exit 10
  }
}
