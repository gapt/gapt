package gapt.provers.vampire

import java.io.IOException

import gapt.formats.StringInputFile
import gapt.formats.tptp.TptpFOLExporter
import gapt.formats.tptp.TptpProofParser
import gapt.proofs.resolution.ResolutionProof
import gapt.proofs.resolution.fixDerivation
import gapt.proofs.sketch.RefutationSketchToResolution
import gapt.proofs.FOLClause
import gapt.proofs.HOLClause
import gapt.proofs.context.mutable.MutableContext
import gapt.provers.ResolutionProver
import gapt.provers.extractIntroducedDefinitions
import gapt.provers.renameConstantsToFi
import gapt.utils.{ ExternalProgram, Logger, Maybe, runProcess }

object Vampire extends Vampire( commandName = "vampire", extraArgs = Seq() ) {
  val logger = Logger( "vampire" )
}
import Vampire.logger.time
object VampireCASC extends Vampire( commandName = "vampire", extraArgs = Seq( "--mode", "casc" ) )
class Vampire( commandName: String = "vampire", extraArgs: Seq[String] = Seq() ) extends ResolutionProver with ExternalProgram {
  override def getResolutionProof( seq: Iterable[HOLClause] )( implicit ctx: Maybe[MutableContext] ): Option[ResolutionProof] =
    renameConstantsToFi.wrap( seq.toSeq )(
      ( renaming, cnf: Seq[HOLClause] ) => {
        val labelledCNF = cnf.zipWithIndex.map { case ( clause, index ) => s"formula$index" -> clause.asInstanceOf[FOLClause] }.toMap
        val tptpIn = TptpFOLExporter.exportLabelledCNF( labelledCNF ).toString
        val output = time( "vampire" ) {
          runProcess.withTempInputFile(
            commandName +: "-p" +: "tptp" +: extraArgs,
            tptpIn ).split( "\n" )
        }
        extractRefutation( output ) match {
          case Some( refutationLines ) =>
            val sketch = time( "tptp_parse" ) {
              TptpProofParser.parse( StringInputFile( refutationLines.mkString( "\n" ) ) )._2
            }
            val Right( resolution ) = time( "replay" ) { RefutationSketchToResolution( sketch ) }
            Some( time( "fix_derivation" ) { fixDerivation( resolution, cnf ) } )
          case None =>
            require( output.exists( l => l.startsWith( "% SZS status Satisfiable " ) || l == "Satisfiable!" ) )
            None
        }
      } ).map { resolution =>
        extractIntroducedDefinitions( resolution )
        resolution
      }

  private def extractRefutation( lines: Array[String] ): Option[Array[String]] =
    if ( lines.exists( _.startsWith( "Refutation found" ) ) ) {
      // Vampire 4.1
      Some( lines.drop( 1 ).takeWhile( !_.startsWith( "---" ) ) )
    } else if ( lines.exists( _.startsWith( "% SZS status Unsatisfiable " ) ) ) {
      // Vampire 4.2
      Some( lines.dropWhile( !_.startsWith( "% SZS output start Proof" ) ).
        takeWhile( !_.startsWith( "% SZS output end Proof" ) ) )
    } else {
      None
    }

  override val isInstalled: Boolean =
    try {
      runProcess( commandName +: extraArgs :+ "--version" )
      true
    } catch {
      case ex: IOException => false
    }
}

