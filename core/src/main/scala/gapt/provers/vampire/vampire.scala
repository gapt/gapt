package gapt.provers.vampire

import java.io.IOException

import gapt.formats.StringInputFile
import gapt.formats.tptp.TPTPFOLExporter
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
import gapt.utils.ExternalProgram
import gapt.utils.Maybe
import gapt.utils.runProcess

object Vampire extends Vampire( commandName = "vampire", extraArgs = Seq() )
object VampireCASC extends Vampire( commandName = "vampire", extraArgs = Seq( "--mode", "casc" ) )
class Vampire( commandName: String = "vampire", extraArgs: Seq[String] = Seq() ) extends ResolutionProver with ExternalProgram {
  override def getResolutionProof( seq: Traversable[HOLClause] )( implicit ctx: Maybe[MutableContext] ): Option[ResolutionProof] =
    renameConstantsToFi.wrap( seq.toSeq )(
      ( renaming, cnf: Seq[HOLClause] ) => {
        val labelledCNF = cnf.zipWithIndex.map { case ( clause, index ) => s"formula$index" -> clause.asInstanceOf[FOLClause] }.toMap
        val tptpIn = TPTPFOLExporter.exportLabelledCNF( labelledCNF ).toString
        val output = runProcess.withTempInputFile(
          commandName +: "-p" +: "tptp" +: extraArgs,
          tptpIn ).split( "\n" )
        if ( output.exists( l => l.startsWith( "Refutation" ) || l.startsWith( "% Refutation" ) ) ) {
          val sketch = TptpProofParser.parse( StringInputFile( output.drop( 1 ).takeWhile( !_.startsWith( "---" ) ).mkString( "\n" ) ) )._2
          val Right( resolution ) = RefutationSketchToResolution( sketch )
          Some( fixDerivation( resolution, cnf ) )
        } else None
      } ).map { resolution =>
        extractIntroducedDefinitions( resolution )
        resolution
      }

  override val isInstalled: Boolean =
    try {
      runProcess( commandName +: extraArgs :+ "--version" )
      true
    } catch {
      case ex: IOException => false
    }
}

