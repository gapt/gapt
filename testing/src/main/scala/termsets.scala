package at.logic.gapt.testing
import java.nio.file._

import at.logic.gapt.algorithms.rewriting.TermReplacement
import at.logic.gapt.examples.proofSequences
import at.logic.gapt.expr._
import at.logic.gapt.formats.leanCoP.LeanCoPParser
import at.logic.gapt.proofs.expansionTrees.{ toShallow, FOLInstanceTermEncoding, ExpansionSequent }
import at.logic.gapt.proofs.lk.LKToExpansionProof
import at.logic.gapt.provers.prover9.Prover9Importer
import at.logic.gapt.utils.executionModels.timeout.withTimeout
import at.logic.gapt.utils.glob

import scala.App

import scala.concurrent.duration._

object dumpTermsets extends App {
  val outDir = Paths get "termsets"
  Files createDirectories outDir

  def termsetFromExpansionProof( e: ExpansionSequent ): Set[FOLTerm] =
    simplifyNames( FOLInstanceTermEncoding( toShallow( e ) ) encode e map { _.asInstanceOf[FOLTerm] } )

  def simplifyNames( termset: Set[FOLTerm] ): Set[FOLTerm] = {
    val renaming: Map[LambdaExpression, LambdaExpression] =
      ( constants( termset ).toSeq ++ freeVariables( termset ).toSeq ).sortBy( _.toString ).
        zipWithIndex.map { case ( c, i ) => c -> Const( s"f$i", c.exptype ) }.
        toMap
    termset.map( TermReplacement( _, renaming ).asInstanceOf[FOLTerm] )
  }

  def termToString( t: FOLTerm ): String = t match {
    case FOLConst( f )          => s"$f"
    case FOLFunction( f, args ) => s"$f(${args map termToString mkString ","})"
  }

  def writeTermset( outFile: Path, termset: Set[FOLTerm] ) =
    Files.write( outFile, termset.map( termToString ).toSeq.sorted.map( _ + "\n" ).mkString.getBytes( "UTF-8" ) )

  def betterForeach[A]( xs: Traversable[A] )( f: A => Unit ): Unit = {
    var done = 0
    xs.par foreach { x =>
      try withTimeout( 2 minutes ) {
        println( s"[${( done * 100 ) / xs.size}%] $x" )
        done += 1
        f( x )
      } catch {
        case t: Throwable =>
          println( s"$x failed" )
          t.printStackTrace()
      }
    }
  }

  println( "Proof sequences" )
  betterForeach( proofSequences ) { proofSeq =>
    Stream.from( 1 ).map { i =>
      println( s"${proofSeq.name}($i)" )
      i -> termsetFromExpansionProof( LKToExpansionProof( proofSeq( i ) ) )
    }.takeWhile( _._2.size < 100 ).foreach {
      case ( i, termset ) =>
        writeTermset( outDir resolve s"proofseq-${proofSeq.name}-$i.termset", termset )
    }
  }

  println( "Prover9 proofs" )
  betterForeach( glob paths "testing/**/prover9/**/*.s.out" ) { p9File =>
    val expansionProof = Prover9Importer expansionProofFromFile p9File.toString

    writeTermset(
      outDir resolve s"p9-${p9File.getParent.getFileName}.termset",
      termsetFromExpansionProof( expansionProof )
    )
  }

  println( "LeanCoP proofs" )
  betterForeach( glob paths "testing/**/leanCoP/**/*.out" ) { leanCoPFile =>
    writeTermset(
      outDir resolve s"leancop-${leanCoPFile.getParent.getFileName}.termset",
      termsetFromExpansionProof( LeanCoPParser getExpansionProof leanCoPFile.toString get )
    )
  }
}