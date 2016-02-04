package at.logic.gapt.provers.vampire

import java.io.IOException

import at.logic.gapt.expr._
import at.logic.gapt.formats.tptp.{ TPTPFOLExporter, TptpProofParser }
import at.logic.gapt.proofs.resolution.{ ResolutionProof, fixDerivation }
import at.logic.gapt.proofs.{ FOLClause, HOLClause }
import at.logic.gapt.proofs.sketch.RefutationSketchToResolution
import at.logic.gapt.provers.{ ResolutionProver, renameConstantsToFi }
import at.logic.gapt.utils.{ ExternalProgram, runProcess }

object Vampire extends Vampire
class Vampire extends ResolutionProver with ExternalProgram {
  override def getResolutionProof( seq: Traversable[HOLClause] ): Option[ResolutionProof] =
    renameConstantsToFi.wrap( seq.toSeq )(
      ( renaming, cnf: Seq[HOLClause] ) => {
        val labelledCNF = cnf.zipWithIndex.map { case ( clause, index ) => s"formula$index" -> clause.asInstanceOf[FOLClause] }.toMap
        val tptpIn = TPTPFOLExporter.exportLabelledCNF( labelledCNF ).toString
        val output = runProcess.withTempInputFile( Seq(
          "vampire", "-p", "tptp"
        ), tptpIn ).split( "\n" )
        if ( output.head startsWith "Refutation" ) {
          val sketch = TptpProofParser.parse( output.drop( 1 ).takeWhile( !_.startsWith( "---" ) ).mkString( "\n" ) )._2
          RefutationSketchToResolution( sketch ) map { fixDerivation( _, cnf ) } toOption
        } else None
      }
    )

  override val isInstalled: Boolean =
    try {
      runProcess( Seq( "vampire", "--version" ) )
      true
    } catch {
      case ex: IOException => false
    }
}

