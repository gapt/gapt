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
      new iProverTptpOutputParser( inputClauseLabels ).parse( proverOutput )

    private val inputClauseLabels: Labels =
      Labels( inputCNF )

    private val tptpInput: String =
      convertInputCnfToTptp

    private def proverOutput: String =
      runIProverOnTptpInput()

    private def runIProverOnTptpInput(): String =
      runProcess.withTempInputFile( iproverOptions, tptpInput )

    private def convertInputCnfToTptp: String =
      TptpFOLExporter.exportLabelledCNF( inputClauseLabels.toMap ).toString
  }

  class iProverTptpOutputParser( val labels: Labels ) {

    def parse( tptpOutput: String ): Option[ResolutionProof] =
      extractTptpDerivationIfPresent( tptpOutput ).map { parseResolutionProof }

    private def parseResolutionProof( tptpDerivation: String ): ResolutionProof = {
      RefutationSketchToResolution( TptpProofParser.parse(
        StringInputFile( tptpDerivation ),
        labels.toMap.view.mapValues { Seq( _ ) }.toMap ) ) match {
        case Right( proof ) => proof
        case Left( error )  => throw new IllegalArgumentException( error.toString )
      }
    }

    private def extractTptpDerivationIfPresent( proverOutput: String ): Option[String] = {
      if ( statusIsUnsatisfiable( proverOutput ) ) {
        Some( extractTptpDerivation( proverOutput ) )
      } else if ( statusIsSatisfiable( proverOutput ) ) {
        None
      } else {
        throw new IllegalArgumentException
      }
    }

    private def statusIsSatisfiable( proverOutput: String ): Boolean =
      proverOutput
        .split( "\n" )
        .exists( _.startsWith( "% SZS status Satisfiable" ) )

    private def statusIsUnsatisfiable( proverOutput: String ): Boolean =
      proverOutput
        .split( "\n" )
        .exists( _.startsWith( "% SZS status Unsatisfiable" ) )

    private def extractTptpDerivation( proverOutput: String ): String = {
      proverOutput
        .split( "\n" )
        .dropWhile( !_.startsWith( "% SZS output start CNFRefutation" ) )
        .drop( 1 ).
        takeWhile( !_.startsWith( "% SZS output end CNFRefutation" ) ).
        mkString( "\n" )
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
