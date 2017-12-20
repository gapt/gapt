package at.logic.gapt.provers.iprover

import java.io.IOException

import at.logic.gapt.expr._
import at.logic.gapt.formats.StringInputFile
import at.logic.gapt.formats.tptp.{ TPTPFOLExporter, TptpProofParser }
import at.logic.gapt.proofs.resolution.ResolutionProof
import at.logic.gapt.proofs.sketch.RefutationSketchToResolution
import at.logic.gapt.proofs.{ FOLClause, HOLClause, MutableContext }
import at.logic.gapt.provers.{ ResolutionProver, renameConstantsToFi }
import at.logic.gapt.utils.{ ExternalProgram, Maybe, runProcess }

object IProver extends IProver

class IProver extends ResolutionProver with ExternalProgram {
  override def getResolutionProof( seq: Traversable[HOLClause] )( implicit ctx: Maybe[MutableContext] ): Option[ResolutionProof] =
    renameConstantsToFi.wrap( seq.toSeq )(
      ( renaming, cnf: Seq[HOLClause] ) => {
        val labelledCNF = cnf.zipWithIndex.map { case ( clause, index ) => s"formula$index" -> clause.asInstanceOf[FOLClause] }.toMap
        val tptpIn = TPTPFOLExporter.exportLabelledCNF( labelledCNF ).toString
        val output = runProcess.withTempInputFile( Seq(
          "iproveropt",
          "--schedule", "none",
          "--pure_diseq_elim", "false",
          "--splitting_mode", "none" ), tptpIn )
        val lines = output.split( "\n" ).toSeq
        if ( lines.exists( _.startsWith( "% SZS status Unsatisfiable" ) ) ) {
          val tptpDerivation = lines.
            dropWhile( !_.startsWith( "% SZS output start CNFRefutation" ) ).drop( 1 ).
            takeWhile( !_.startsWith( "% SZS output end CNFRefutation" ) ).
            mkString( "\n" )
          RefutationSketchToResolution( TptpProofParser.parse(
            StringInputFile( tptpDerivation ),
            labelledCNF mapValues { Seq( _ ) } ) ) match {
            case Right( proof ) => Some( proof )
            case Left( error )  => throw new IllegalArgumentException( error.toString )
          }
        } else if ( lines.exists( _.startsWith( "% SZS status Satisfiable" ) ) ) {
          None
        } else {
          throw new IllegalArgumentException
        }
      } )

  override val isInstalled: Boolean =
    try {
      runProcess.withExitValue( Seq( "iproveropt" ) )._1 == 2
      true
    } catch {
      case ex: IOException => false
    }
}
