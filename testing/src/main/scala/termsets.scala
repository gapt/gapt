package at.logic.gapt.testing
import java.nio.file._

import at.logic.gapt.algorithms.rewriting.NameReplacement
import at.logic.gapt.expr._
import at.logic.gapt.formats.leanCoP.LeanCoPParser
import at.logic.gapt.proofs.expansionTrees.{ toShallow, InstanceTermEncoding, ExpansionSequent }
import at.logic.gapt.provers.prover9.Prover9Importer
import at.logic.gapt.utils.executionModels.timeout.withTimeout
import org.apache.commons.lang3.exception.ExceptionUtils

import scala.App

import scala.concurrent.duration._

object dumpTermsets extends App {
  val outDir = Paths get "termsets"
  Files createDirectories outDir

  def termsetFromExpansionProof( e: ExpansionSequent ): Set[FOLTerm] =
    simplifyNames( new InstanceTermEncoding( toShallow( e ) ) encode e toSet )

  def simplifyNames( termset: Set[FOLTerm] ): Set[FOLTerm] = {
    val renaming = constants( termset ).toSeq.sortBy( _.toString ).
      zipWithIndex.map { case ( FOLFunctionHead( sym, arity ), i ) => sym -> ( arity, s"f$i" ) }.
      toMap
    termset.map( NameReplacement( _, renaming ) )
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

  println( "Prover9 proofs" )
  betterForeach( RegressionTests.prover9Proofs.map( _.toPath ) ) { p9File =>
    writeTermset(
      outDir resolve s"p9-${p9File.getParent.getFileName}.termset",
      termsetFromExpansionProof( Prover9Importer expansionProofFromFile p9File.toString )
    )
  }

  println( "LeanCoP proofs" )
  betterForeach( RegressionTests.leancopProofs.map( _.toPath ) ) { leanCoPFile =>
    writeTermset(
      outDir resolve s"leancop-${leanCoPFile.getParent.getFileName}.termset",
      termsetFromExpansionProof( LeanCoPParser getExpansionProof leanCoPFile.toString get )
    )
  }
}