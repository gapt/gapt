package at.logic.gapt.provers.eprover

import java.io.IOException

import at.logic.gapt.expr._
import at.logic.gapt.formats.tptp.{ TPTPFOLExporter, TptpProofParser, tptpToString }
import at.logic.gapt.proofs.resolution.ResolutionProof
import at.logic.gapt.proofs.{ FOLClause, HOLClause }
import at.logic.gapt.proofs.sketch.RefutationSketchToResolution
import at.logic.gapt.provers.{ ResolutionProver, renameConstantsToFi }
import at.logic.gapt.utils.{ ExternalProgram, runProcess, withTempFile }

object EProver extends EProver
class EProver extends ResolutionProver with ExternalProgram {
  override def getResolutionProof( seq: Traversable[HOLClause] ): Option[ResolutionProof] =
    renameConstantsToFi.wrap( seq.toSeq )(
      ( renaming, cnf: Seq[HOLClause] ) => {
        val labelledCNF = cnf.zipWithIndex.map { case ( clause, index ) => s"formula$index" -> clause.asInstanceOf[FOLClause] }.toMap
        val tptpIn = TPTPFOLExporter.exportLabelledCNF( labelledCNF ).toString
        val output = runProcess.withTempInputFile( Seq( "eproof", "--tptp3-format" ), tptpIn )
        val lines = output.split( "\n" )
        if ( lines.contains( "# SZS status Unsatisfiable" ) )
          RefutationSketchToResolution( TptpProofParser.parse(
            lines.filterNot( _ startsWith "# " ).mkString( "\n" ),
            labelledCNF mapValues { Seq( _ ) }
          ) ).toOption
        else None
      }
    )

  override val isInstalled: Boolean =
    try {
      runProcess( Seq( "eproof", "--version" ) )
      true
    } catch {
      case ex: IOException => false
    }
}
