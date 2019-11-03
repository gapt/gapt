package gapt.provers.iprover

import java.io.IOException

import gapt.expr._
import gapt.formats.StringInputFile
import gapt.proofs.context.mutable.MutableContext
import gapt.formats.tptp.{ TptpFOLExporter, TptpProofParser }
import gapt.proofs.resolution.ResolutionProof
import gapt.proofs.sketch.RefutationSketchToResolution
import gapt.proofs.{ FOLClause, HOLClause }
import gapt.provers.{ ResolutionProver, renameConstantsToFi }
import gapt.utils.{ ExternalProgram, Maybe, runProcess }

object IProver extends IProver

class IProver extends ResolutionProver with ExternalProgram {

  val iproverOptions = Seq(
    "iproveropt",
    "--schedule", "none",
    "--pure_diseq_elim", "false",
    "--splitting_mode", "none",
    "--sub_typing", "false",
    "--tptp_safe_out", "true" )

  override def getResolutionProof( seq: Iterable[HOLClause] )( implicit ctx: Maybe[MutableContext] ): Option[ResolutionProof] =
    renameConstantsToFi.wrap( seq.toSeq )(
      ( _, cnf: Seq[HOLClause] ) =>
        new IProverInvoker( cnf.map { _.asInstanceOf[FOLClause] } )
          .getResolutionProof() )

  private class IProverInvoker( val inputCNF: Seq[FOLClause] ) {

    def getResolutionProof(): Option[ResolutionProof] =
      runIProverOn( tptpInput ).tptpDerivation.map { parseResolutionProof }

    private def parseResolutionProof( tptpDerivation: String ): ResolutionProof =
      new TptpDerivationParser( inputClauseLabels )
        .parseAsResolutionProof( tptpDerivation )

    private val inputClauseLabels: Labels =
      Labels( inputCNF )

    private val tptpInput: String =
      convertInputCnfToTptp

    private def runIProverOn( input: String ): IProverOutput =
      new IProverOutput( iProver( input ) )

    private def iProver( input: String ): String =
      runProcess.withTempInputFile( iproverOptions, input )

    private def convertInputCnfToTptp: String =
      TptpFOLExporter.exportLabelledCNF( inputClauseLabels.toMap ).toString
  }

  class IProverOutput( val rawOutput: String ) {

    private val outputLines: Array[String] =
      rawOutput.split( "\n" )

    val tptpDerivation: Option[String] =
      if ( statusIsUnsatisfiable )
        Some( extractTptpDerivation )
      else if ( isStatusSatisfiable )
        None
      else
        throw new IllegalArgumentException( "invalid prover output" )

    private def isStatusSatisfiable: Boolean =
      outputLines.exists( _.startsWith( "% SZS status Satisfiable" ) )

    private def statusIsUnsatisfiable: Boolean =
      outputLines.exists( _.startsWith( "% SZS status Unsatisfiable" ) )

    private def extractTptpDerivation: String = {
      outputLines
        .dropWhile( !_.startsWith( "% SZS output start CNFRefutation" ) )
        .drop( 1 ).
        takeWhile( !_.startsWith( "% SZS output end CNFRefutation" ) ).
        mkString( "\n" )
    }
  }

  class TptpDerivationParser( val labels: Labels ) {

    def parseAsResolutionProof( tptpDerivation: String ): ResolutionProof = {
      RefutationSketchToResolution( TptpProofParser.parse(
        StringInputFile( tptpDerivation ),
        labels.toMap.view.mapValues { Seq( _ ) }.toMap ) ) match {
        case Right( proof ) => proof
        case Left( error )  => throw new IllegalArgumentException( error.toString )
      }
    }
  }

  case class Labels( cnf: Seq[FOLClause] ) {

    def toMap: Map[String, FOLClause] =
      labelledCNF

    private val labelledCNF: Map[String, FOLClause] =
      labelCNF( cnf )

    private def labelCNF( cnf: Seq[FOLClause] ): Map[String, FOLClause] =
      cnf.zipWithIndex.map {
        case ( clause, index ) =>
          s"formula$index" -> clause.asInstanceOf[FOLClause]
      }.toMap
  }

  override val isInstalled: Boolean =
    try {
      runProcess.withExitValue( Seq( "iproveropt" ) )._1 == 2
      true
    } catch {
      case ex: IOException => false
    }
}
