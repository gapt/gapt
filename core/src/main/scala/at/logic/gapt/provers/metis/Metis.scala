package at.logic.gapt.provers.metis

import java.io.IOException

import at.logic.gapt.expr._
import at.logic.gapt.formats.tptp.{ TPTPFOLExporter, TptpProofParser }
import at.logic.gapt.proofs.resolution.ResolutionProof
import at.logic.gapt.proofs.sketch.RefutationSketchToResolution
import at.logic.gapt.proofs.{ FOLClause, HOLClause }
import at.logic.gapt.provers.{ ResolutionProver, renameConstantsToFi }
import at.logic.gapt.utils.{ ExternalProgram, runProcess }

import scalaz.Success

object Metis extends Metis

class Metis extends ResolutionProver with ExternalProgram {
  override def getResolutionProof( seq: Traversable[HOLClause] ): Option[ResolutionProof] =
    renameConstantsToFi.wrap( seq.toSeq )(
      ( renaming, cnf: Seq[HOLClause] ) => {
        val labelledCNF = cnf.zipWithIndex.map { case ( clause, index ) => s"formula$index" -> clause.asInstanceOf[FOLClause] }.toMap
        val tptpIn = TPTPFOLExporter.exportLabelledCNF( labelledCNF ).toString
        val output = runProcess.withTempInputFile( Seq( "metis", "--show", "proof" ), tptpIn )
        val lines = output.split( "\n" ).toSeq
        if ( lines.exists( _.startsWith( "SZS status Unsatisfiable" ) ) ) {
          val tptpDerivation = lines.
            dropWhile( !_.startsWith( "SZS output start CNFRefutation " ) ).drop( 1 ).
            takeWhile( !_.startsWith( "SZS output end CNFRefutation " ) ).
            mkString( "\n" )
          RefutationSketchToResolution( TptpProofParser.parse( tptpDerivation, labelledCNF mapValues {
            Seq( _ )
          } ) ) match {
            case Success( proof ) => Some( proof )
          }
        } else if ( lines.exists( _.startsWith( "SZS status Satisfiable" ) ) ) {
          None
        } else {
          throw new IllegalArgumentException
        }
      }
    )

  override val isInstalled: Boolean =
    try {
      runProcess( Seq( "metis", "--version" ) )
      true
    } catch {
      case ex: IOException => false
    }
}
