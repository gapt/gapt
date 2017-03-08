package at.logic.gapt.testing

import at.logic.gapt.expr._
import at.logic.gapt.proofs.expansion.InstanceTermEncoding
import at.logic.gapt.proofs.loadExpansionProof

import scala.App
import ammonite.ops._

object dumpTermset extends App {
  val Array( inputFileName, outputFileName ) = args
  val inputPath = Path( inputFileName, pwd )
  val outputPath = Path( outputFileName, pwd )

  def simplifyNames( termset: Set[FOLTerm] ): Set[FOLTerm] = {
    val renaming: Map[Expr, Expr] =
      ( constants( termset ).toSeq ++ freeVariables( termset ).toSeq ).sortBy( _.toString ).
        zipWithIndex.map { case ( c, i ) => c -> Const( s"f$i", c.ty ) }.
        toMap
    termset.map( TermReplacement( _, renaming ).asInstanceOf[FOLTerm] )
  }

  def termToString( t: FOLTerm ): String = t match {
    case FOLConst( f )          => s"$f"
    case FOLFunction( f, args ) => s"$f(${args map termToString mkString ","})"
  }

  def writeTermset( outFile: Path, termset: Set[FOLTerm] ) =
    write.over( outFile, termset.map( termToString ).toSeq.sorted.map( _ + "\n" ).mkString )

  val expansionProof = loadExpansionProof( inputPath )
  val encoding = InstanceTermEncoding( expansionProof.shallow, Ti )
  val termSet = encoding.encode( expansionProof ).map( _.asInstanceOf[FOLTerm] )
  writeTermset( outputPath, simplifyNames( termSet ) )
}