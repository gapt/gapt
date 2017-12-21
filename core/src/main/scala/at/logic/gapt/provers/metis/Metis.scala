package at.logic.gapt.provers.metis

import java.io.IOException

import at.logic.gapt.expr._
import at.logic.gapt.formats.StringInputFile
import at.logic.gapt.formats.tptp.{ TPTPFOLExporter, TptpProofParser }
import at.logic.gapt.proofs.resolution.ResolutionProof
import at.logic.gapt.proofs.sketch.RefutationSketchToResolution
import at.logic.gapt.proofs.{ FOLClause, HOLClause, MutableContext }
import at.logic.gapt.provers.{ ResolutionProver, renameConstantsToFi }
import at.logic.gapt.utils.{ ExternalProgram, Maybe, runProcess }

object Metis extends Metis

class Metis extends ResolutionProver with ExternalProgram {
  override def getResolutionProof( seq: Traversable[HOLClause] )( implicit ctx: Maybe[MutableContext] ): Option[ResolutionProof] =
    renameConstantsToFi.wrap( seq.toSeq )(
      ( renaming, cnf: Seq[HOLClause] ) => {
        val labelledCNF = cnf.zipWithIndex.map { case ( clause, index ) => s"formula$index" -> clause.asInstanceOf[FOLClause] }.toMap
        val tptpIn = TPTPFOLExporter.exportLabelledCNF( labelledCNF ).toString
        val output = runProcess.withTempInputFile( Seq( "metis", "--show", "proof" ), tptpIn )
        val lines = output.split( "\n" ).toSeq
        if ( lines.exists( _.contains( "SZS status Unsatisfiable" ) ) ) {
          val tptpDerivation = lines.
            dropWhile( !_.contains( "SZS output start CNFRefutation " ) ).drop( 1 ).
            takeWhile( !_.contains( "SZS output end CNFRefutation " ) ).
            mkString( "\n" )
          RefutationSketchToResolution( TptpProofParser.parse( StringInputFile( tptpDerivation ), labelledCNF mapValues {
            Seq( _ )
          } ) ) match {
            case Right( proof ) => Some( proof )
            case Left( error )  => throw new IllegalArgumentException( error.toString )
          }
        } else if ( lines.exists( _.contains( "SZS status Satisfiable" ) ) ) {
          None
        } else {
          throw new IllegalArgumentException( s"Cannot parse metis output:\n$output" )
        }
      } )

  override val isInstalled: Boolean =
    try {
      runProcess( Seq( "metis", "--version" ) )
      true
    } catch {
      case ex: IOException => false
    }
}
