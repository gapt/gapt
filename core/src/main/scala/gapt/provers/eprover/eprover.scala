package gapt.provers.eprover

import java.io.IOException

import gapt.expr._
import gapt.formats.StringInputFile
import gapt.proofs.context.mutable.MutableContext
import gapt.formats.tptp.{ TptpFOLExporter, TptpProofParser, TptpToString }
import gapt.proofs.resolution.ResolutionProof
import gapt.proofs.{ FOLClause, HOLClause }
import gapt.proofs.sketch.RefutationSketchToResolution
import gapt.provers.{ ResolutionProver, renameConstantsToFi }
import gapt.utils._

object EProver extends EProver( Seq() ) {
  val logger = Logger( "eprover" )
}
import EProver.logger
class EProver( extraArgs: Seq[String] ) extends ResolutionProver with ExternalProgram {
  override def getResolutionProof( seq: Traversable[HOLClause] )( implicit ctx: Maybe[MutableContext] ): Option[ResolutionProof] =
    renameConstantsToFi.wrap( seq.toSeq )(
      ( renaming, cnf: Seq[HOLClause] ) => {
        val labelledCNF = cnf.zipWithIndex.map { case ( clause, index ) => s"formula$index" -> clause.asInstanceOf[FOLClause] }.toMap
        val tptpIn = TptpFOLExporter.exportLabelledCNF( labelledCNF ).toString
        ( logger.time( "eprover" ) { runProcess.withExitValue( Seq( "eprover", "-p", "--tptp3-format" ) ++ extraArgs, tptpIn ) }: @unchecked ) match {
          case ( 0, output ) =>
            val lines = output.split( "\n" )
            require( lines.contains( "# SZS status Unsatisfiable" ) || lines.contains( "# SZS status ContradictoryAxioms" ) )
            logger.time( "eprover_import" ) {
              val sketch = TptpProofParser.parse(
                StringInputFile( lines.filterNot( _ startsWith "#" ).mkString( "\n" ) ),
                labelledCNF.mapValues( Seq( _ ) ) )
              Some( RefutationSketchToResolution( sketch ).getOrElse( throw new Exception( "Could not reconstruct proof" ) ) )
            }
          case ( 1, output ) =>
            val lines = output.split( "\n" )
            require( lines.contains( "# SZS status Satisfiable" ) )
            None
          case ( exitVal, output ) =>
            throw new IOException( s"Unexpected exit value $exitVal\n$output" )
        }
      } )

  override val isInstalled: Boolean =
    try {
      runProcess( Seq( "eprover", "--version" ) )
      true
    } catch {
      case ex: IOException => false
    }
}
