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

object IProver extends ResolutionProver with ExternalProgram {

  override def getResolutionProof( seq: Iterable[HOLClause] )( implicit ctx: Maybe[MutableContext] ): Option[ResolutionProof] =
    new IProverInstance( new IProverInput( seq.toSeq.map { _.asInstanceOf[FOLClause] } ) ).getResolutionProof()

  override val isInstalled: Boolean =
    try {
      runProcess.withExitValue( Seq( "iproveropt" ) )._1 == 2
      true
    } catch {
      case _: IOException => false
    }
}

class IProverInstance( val input: IProverInput ) {

  private val iproverOptions = Seq(
    "iproveropt",
    "--schedule", "none",
    "--pure_diseq_elim", "false",
    "--splitting_mode", "none",
    "--sub_typing", "false",
    "--tptp_safe_out", "true" )

  def getResolutionProof(): Option[ResolutionProof] =
    runIProverOn( input.tptpWithSafeNames )
      .tptpDerivation
      .map { parseResolutionProof }
      .map { revertToOriginalNames }

  private def revertToOriginalNames(
    refutation: ResolutionProof ): ResolutionProof = {
    val originalNames: Map[Const, Const] = input.originalNamesToSafeNames.map( _.swap )
    TermReplacement.hygienic( refutation, originalNames )
  }

  private def parseResolutionProof( tptpDerivation: String ): ResolutionProof =
    new TptpDerivationParser( input.clauseLabels )
      .parseAsResolutionProof( tptpDerivation )

  private def runIProverOn( input: String ): IProverOutput =
    new IProverOutput( iProver( input ) )

  private def iProver( input: String ): String =
    runProcess.withTempInputFile( iproverOptions, input )

}

class IProverInput( val cnf: Seq[FOLClause] ) {

  private type Renaming = Map[Const, Const]

  val ( cnfWithSafeNames, originalNamesToSafeNames ) = useSafeNames( cnf )

  val clauseLabels: Labels = Labels( cnfWithSafeNames )

  val tptpWithSafeNames: String =
    TptpFOLExporter.exportLabelledCNF( clauseLabels.toMap ).toString

  private def useSafeNames( cnf: Seq[FOLClause] ): ( Seq[FOLClause], Renaming ) = {
    val ( cnfWithSafeNames, safeNames ) =
      renameConstantsToFi[Seq[HOLClause], Seq[HOLClause]]( cnf )
    ( cnfWithSafeNames.map { _.asInstanceOf[FOLClause] }, safeNames )
  }

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

