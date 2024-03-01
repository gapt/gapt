package gapt.provers.metis

import java.io.IOException

import gapt.formats.StringInputFile
import gapt.formats.tptp.TptpFOLExporter
import gapt.formats.tptp.TptpProofParser
import gapt.proofs.resolution.ResolutionProof
import gapt.proofs.resolution.resolutionProofsAreReplaceable
import gapt.proofs.sketch.RefutationSketchToResolution
import gapt.proofs.FOLClause
import gapt.proofs.HOLClause
import gapt.proofs.context.mutable.MutableContext
import gapt.provers.ResolutionProver
import gapt.provers.renameConstantsToFi
import gapt.utils.ExternalProgram
import gapt.utils.Maybe
import gapt.utils.runProcess

object Metis extends Metis

class Metis extends ResolutionProver with ExternalProgram {
  override def getResolutionProof( seq: Iterable[HOLClause] )( implicit ctx: Maybe[MutableContext] ): Option[ResolutionProof] =
    renameConstantsToFi.wrap( seq.toSeq )(
      ( renaming, cnf: Seq[HOLClause] ) => {
        val labelledCNF = cnf.zipWithIndex.map { case ( clause, index ) => s"formula$index" -> clause.asInstanceOf[FOLClause] }.toMap
        val tptpIn = TptpFOLExporter.exportLabelledCNF( labelledCNF ).toString
        val output = runProcess.withTempInputFile( Seq( "metis", "--show", "proof" ), tptpIn )
        val lines = output.split( "\n" ).toSeq
        if ( lines.exists( _.contains( "SZS status Unsatisfiable" ) ) ) {
          val tptpDerivation = lines.
            dropWhile( !_.contains( "SZS output start CNFRefutation " ) ).drop( 1 ).
            takeWhile( !_.contains( "SZS output end CNFRefutation " ) ).
            mkString( "\n" )
          RefutationSketchToResolution( TptpProofParser.parse( StringInputFile( tptpDerivation ), labelledCNF.view.mapValues {
            Seq( _ )
          }.toMap ) ) match {
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
