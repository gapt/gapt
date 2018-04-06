package gapt.provers.vampire

import java.io.IOException

import gapt.expr._
import gapt.formats.StringInputFile
import gapt.formats.tptp.{ TPTPFOLExporter, TptpProofParser }
import gapt.proofs.resolution.{ ResolutionProof, fixDerivation }
import gapt.proofs.{ FOLClause, HOLClause, MutableContext }
import gapt.proofs.sketch.RefutationSketchToResolution
import gapt.provers.{ ResolutionProver, extractIntroducedDefinitions, renameConstantsToFi }
import gapt.utils.{ ExternalProgram, Maybe, runProcess }

object Vampire extends Vampire( commandName = "vampire", extraArgs = Seq() )
class Vampire( commandName: String = "vampire", extraArgs: Seq[String] = Seq() ) extends ResolutionProver with ExternalProgram {
  override def getResolutionProof( seq: Traversable[HOLClause] )( implicit ctx: Maybe[MutableContext] ): Option[ResolutionProof] =
    renameConstantsToFi.wrap( seq.toSeq )(
      ( renaming, cnf: Seq[HOLClause] ) => {
        val labelledCNF = cnf.zipWithIndex.map { case ( clause, index ) => s"formula$index" -> clause.asInstanceOf[FOLClause] }.toMap
        val tptpIn = TPTPFOLExporter.exportLabelledCNF( labelledCNF ).toString
        val output = runProcess.withTempInputFile(
          commandName +: "-p" +: "tptp" +: extraArgs,
          tptpIn ).split( "\n" )
        if ( output.head startsWith "Refutation" ) {
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

